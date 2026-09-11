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
      // asks for what it is missing, and only once per index, so there is no
      // guard here against a render that answers its own request.
      const missing = action.indices.filter((i) => state.eventRows[i] === undefined);
      if (missing.length === 0) return done(state);
      return query(state, "eventRows", [missing]);
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
      if (action.error) return done(next);
      switch (action.method) {
        case "details":
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
          return done({ ...next, eventRows });
        }
        default:
          return done(next);
      }
    }

    case "hoverSpan":
      // The view hands over a span; the bundle it belongs to is what the
      // highlight is keyed by, and the outline already knows which that is.
      return done({ ...state, hoveredBundle: bundleOf(state.outline, action.ref) });

    case "unhoverSpan":
      return done({ ...state, hoveredBundle: null });

    case "scrollToHistogram":
      return done({ ...state, scrollToHistogram: action.id });

    case "scrolled":
      // An unknown `what` is a no-op. The view is the only thing that
      // dispatches this, but a typo there should clear neither request.
      if (action.what === "entity") return done({ ...state, scrollToEntity: null });
      if (action.what === "histogram") return done({ ...state, scrollToHistogram: null });
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
