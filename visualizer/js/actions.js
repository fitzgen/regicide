// Layer 4: actions and handlers.
//
// `handleAction` is the only place in the page that decides anything. It is
// pure: same input, same output, no DOM, no worker, and neither argument is
// mutated. `queries` is what the glue posts to the worker; a response comes
// back in as another action.

import { entityKey, sameEntity } from "./entities.js";

// How many details results to keep. A user walking a long trail accumulates
// one per distinct entity, and each holds a whole pane's worth of fields.
const DETAILS_CACHE_SIZE = 50;

// Apply `action` to `state`.
//
// Returns the next state and the queries the glue should send. A query's
// `method` is echoed back with its result, because one `queryResult` action
// carries responses for every query kind and dispatching on the shape of the
// result would be guesswork.
export function handleAction(state, action) {
  switch (action.type) {
    case "loaded": {
      // The blob is readable, so the panes can be asked for. The load
      // response itself is not a query result -- it settles whether the page
      // can show anything at all -- so this is where the page starts.
      //
      // The empty search goes out now rather than when the event tab is first
      // shown: it is the whole log, it is what the tab opens on, and asking
      // for it here means the tab is populated the moment it appears.
      //
      // The histograms go out with them rather than when their tab is first
      // shown: they are already computed, they never change, and asking for
      // them here means every tab is drawn before the user reaches it.
      const search = { ...state.search, query: "", pending: true };
      return queries({ ...state, search }, [
        { method: "functionOutline", args: [] },
        { method: "searchEvents", args: [""] },
        { method: "histograms", args: [] },
        { method: "histogramGroups", args: [] },
      ]);
    }

    case "selectTab":
      // The tab and nothing else: the other tabs' state survives a round trip
      // away and back, which is what a user expects after checking the event
      // log and returning to where they were in the function.
      return done({ ...state, tab: action.tab });

    case "clickEntity": {
      // An event is a position in the log, not an entity with a pane -- the
      // model answers `null` for one -- so the click means "show me it in the
      // log" and never touches the breadcrumb trail.
      if (action.ref.kind === "EventIndex") return showEvent(state, action.ref.index);

      // Clicking the already-active entity re-selects it rather than pushing:
      // a `[v3, v3]` trail says nothing the single crumb did not, and the
      // re-select still scrolls the pane back to it.
      if (sameEntity(state.breadcrumbs[state.activeBreadcrumb], action.ref)) {
        return select(state, state.breadcrumbs, state.activeBreadcrumb);
      }

      // Otherwise clear everything after the active breadcrumb, then push.
      const kept = state.breadcrumbs.slice(0, state.activeBreadcrumb + 1);
      const breadcrumbs = [...kept, action.ref];
      return select(state, breadcrumbs, breadcrumbs.length - 1);
    }

    case "clickBreadcrumb": {
      // No truncation, unlike `clickEntity`. That asymmetry is the whole point
      // of the bar: it is how a user goes back up the trail and forward again.
      if (action.index < 0 || action.index >= state.breadcrumbs.length) return done(state);
      return select(state, state.breadcrumbs, action.index);
    }

    case "search": {
      // Debounced in `main.js`, not here: a keystroke per query over a large
      // log is the exact thing the worker was introduced to avoid, and the
      // handler stays pure and synchronous by not knowing about it.
      const search = { ...state.search, query: action.query, pending: true };
      return query({ ...state, search }, "searchEvents", [action.query]);
    }

    case "needEventRows": {
      // The view asks for the rows of the window it is about to draw. It only
      // asks for what it is missing and what is not already in flight, so
      // there is no guard here against a render that answers its own request.
      const missing = action.indices.filter(
        (i) => state.eventRows[i] === undefined && state.askedRows[i] === undefined,
      );
      if (missing.length === 0) return done(state);
      return query({ ...state, askedRows: withRows(state.askedRows, missing) }, "eventRows", [
        missing,
      ]);
    }

    case "clickEntityFromEvent": {
      // The tab first, then exactly what a click in the function pane does.
      // Delegating rather than repeating is what keeps one set of rules for
      // the breadcrumb trail, the selection, and the scroll.
      const click = { type: "clickEntity", ref: action.entity };
      return handleAction({ ...state, tab: "function" }, click);
    }

    case "queryResult": {
      const pending = { ...state.pending };
      delete pending[action.id];
      const next = { ...state, pending, error: action.error || null };
      if (action.error) return done(failed(next, action));
      switch (action.method) {
        case "details":
          // `null` when the model has nothing to say about the ref. There is
          // nothing to cache, but the pending key still has to clear or the
          // pane reads "Loading..." for good. The key comes from the echoed
          // args, because a `null` carries no ref to derive it from.
          if (action.result === null) return done(clearPendingDetails(next, action.args));
          return done(cacheDetails(next, action.result));
        case "functionOutline":
          return done({ ...next, outline: action.result });
        case "histograms":
          return done({ ...next, histograms: action.result });
        case "histogramGroups":
          return done({ ...next, histogramGroups: action.result });
        case "searchEvents": {
          // The one place a stale result is dropped rather than cached. A
          // debounced search guarantees out-of-order responses, the query text
          // lives in the state so the comparison is a string compare, and a
          // result for text the user has moved on from has no cache value --
          // unlike a details result, which is a breadcrumb away from being
          // wanted again.
          if ((action.args || [])[0] !== next.search.query) return done(next);
          return done({
            ...next,
            search: { ...next.search, results: action.result, pending: false },
          });
        }
        case "eventRows": {
          const eventRows = { ...next.eventRows };
          for (const row of action.result) eventRows[row.index] = row;
          return done({ ...next, eventRows, askedRows: withoutRows(next, action.args) });
        }
        default:
          return done(next);
      }
    }

    case "hoverEntity": {
      // Two things at once, from the one gesture: the bundle-wide dim, keyed
      // by the bundle the outline placed the span in -- a ref that is not a
      // span reaches no bar and so dims nothing, exactly as before -- and the
      // details preview.
      //
      // No breadcrumb, no selection, no scroll: hovering is looking, and the
      // trail is a record of where the user chose to go.
      const key = entityKey(action.ref);
      const next = {
        ...state,
        hovered: action.ref,
        hoveredBundle: bundleOf(state.outline, action.ref),
      };
      // The pointer crosses a lot of entities on its way somewhere, so only a
      // cache miss is worth a query.
      if (state.details[key] !== undefined) return done(next);
      return query({ ...next, pendingDetails: key }, "details", [action.ref]);
    }

    case "unhoverEntity":
      // Which restores the active breadcrumb's details, because that is what
      // the pane falls back to.
      return done({ ...state, hovered: null, hoveredBundle: null });

    case "scrollToHistogram":
      return done({ ...state, scrollToHistogram: action.id });

    case "scrolled":
      // An unknown `what` is a no-op. The view is the only thing that
      // dispatches this, but a typo there should clear none of the requests.
      if (action.what === "entity") return done({ ...state, scrollToEntity: null });
      if (action.what === "histogram") return done({ ...state, scrollToHistogram: null });
      if (action.what === "event") return done({ ...state, scrollToEvent: null });
      return done(state);

    default:
      return done(state);
  }
}

// Make `breadcrumbs[active]` the selection, scroll to it, and ask for its
// details.
function select(state, breadcrumbs, active) {
  const ref = breadcrumbs[active];
  const next = {
    ...state,
    breadcrumbs,
    activeBreadcrumb: active,
    selected: ref,
    scrollToEntity: ref,
    pendingDetails: entityKey(ref),
  };
  return query(next, "details", [ref]);
}

// Show the event log, scrolled to one event.
//
// No breadcrumb and no selection: the trail is a record of the entities a user
// chose to look at, and an event is a place rather than a thing.
function showEvent(state, index) {
  const next = { ...state, tab: "events", scrollToEvent: index };
  // The list draws the current results and nothing else, so an event the
  // filter is hiding has nowhere to be scrolled to and the query has to go.
  // A filter that already shows it is left alone -- the user put it there, and
  // the scroll works within it.
  if ((state.search.results || []).includes(index)) return done(next);
  const search = { ...next.search, query: "", pending: true };
  return query({ ...next, search }, "searchEvents", [""]);
}

// Store a details result. Always: by the time one arrives, nothing in it says
// which click it answered, and a result for an entity the user has clicked
// away from is not stale but a warm cache entry for a breadcrumb they are one
// click from returning to. Freshness is then a rendering question -- the pane
// reads the cache at the *selected* key -- and an out-of-order arrival cannot
// show the wrong entity.
function cacheDetails(state, result) {
  const key = entityKey(result.ref);
  const details = { ...state.details, [key]: result };
  const detailsOrder = [...state.detailsOrder.filter((k) => k !== key), key];
  while (detailsOrder.length > DETAILS_CACHE_SIZE) delete details[detailsOrder.shift()];
  return {
    ...state,
    details,
    detailsOrder,
    // Only the query this answers: another is still in flight.
    pendingDetails: state.pendingDetails === key ? null : state.pendingDetails,
  };
}

// Undo what a query that failed had marked as in flight.
//
// The error banner says something went wrong, but a pane left pending says
// "Loading..." forever: the details pane short-circuits on a cache hit alone,
// so even clicking away and back would not retry. Only this query's marks are
// cleared -- another may still be in flight.
function failed(state, action) {
  switch (action.method) {
    case "details":
      return clearPendingDetails(state, action.args);
    case "searchEvents":
      // The results stay: stale rows under an error banner beat an empty list,
      // and the query text in the state still says what they answered.
      return { ...state, search: { ...state.search, pending: false } };
    case "eventRows":
      // Un-ask them, or the rows this query was for stay "..." for the life of
      // the page: the view asks once per index and would never ask again.
      return { ...state, askedRows: withoutRows(state, action.args) };
    default:
      return state;
  }
}

// `asked` plus `indices`.
function withRows(asked, indices) {
  const next = { ...asked };
  for (const i of indices) next[i] = true;
  return next;
}

// `state.askedRows` minus the indices an `eventRows` query asked for, which
// are the first of its echoed args.
function withoutRows(state, args) {
  const next = { ...state.askedRows };
  for (const i of (args || [])[0] || []) delete next[i];
  return next;
}

// Clear the pending details key, given the args of the query that answered.
//
// Only that query's key: another may still be in flight, and clearing the
// field outright would make its pane say "this entity has no details" the
// moment a different one came back empty.
function clearPendingDetails(state, args) {
  const ref = (args || [])[0];
  if (!ref) return state;
  const key = entityKey(ref);
  return state.pendingDetails === key ? { ...state, pendingDetails: null } : state;
}

// The bundle a span was placed in, or `null` for a span that reached none.
function bundleOf(outline, span) {
  const bar = (outline ? outline.bars : []).find((bar) => sameEntity(bar.span, span));
  return bar === undefined ? null : bar.bundle;
}

// A state change with nothing to ask the worker.
function done(state) {
  return { state, queries: [] };
}

// A state change that also asks the worker something.
function query(state, method, args) {
  return queries(state, [{ method, args }]);
}

// The same, for more than one question at once. Ids come from the state, so
// they have to be handed out in order rather than each call reading the same
// `nextQueryId`.
function queries(state, list) {
  let id = state.nextQueryId;
  const pending = { ...state.pending };
  const sent = list.map(({ method, args }) => {
    pending[id] = method;
    return { id: id++, method, args };
  });
  return {
    state: { ...state, nextQueryId: id, pending },
    queries: sent,
  };
}
