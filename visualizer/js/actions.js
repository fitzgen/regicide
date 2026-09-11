// Layer 4: actions and handlers.
//
// `handleAction` is the only place in the page that decides anything. It is
// pure: same input, same output, no DOM, no worker, and neither argument is
// mutated. `queries` is what the glue posts to the worker; a response comes
// back in as another action.

import { entityKey } from "./entities.js";

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
    case "selectTab":
      // The tab and nothing else: the other tabs' state survives a round trip
      // away and back, which is what a user expects after checking the event
      // log and returning to where they were in the function.
      return done({ ...state, tab: action.tab });

    case "clickEntity": {
      // Clear everything after the active breadcrumb, then push. Clicking the
      // already-active entity pushes a duplicate, which is honest about what
      // the user did.
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
      const search = { ...state.search, query: action.query, pending: true };
      return query({ ...state, search }, "searchEvents", [action.query]);
    }

    case "queryResult": {
      const pending = { ...state.pending };
      delete pending[action.id];
      const next = { ...state, pending, error: action.error || null };
      if (action.error) return done(next);
      switch (action.method) {
        case "details":
          return done(cacheDetails(next, action.result));
        case "searchEvents":
          return done({
            ...next,
            search: { ...next.search, results: action.result, pending: false },
          });
        default:
          return done(next);
      }
    }

    case "hoverSpan":
      return done({ ...state, hover: action.ref });

    case "unhoverSpan":
      return done({ ...state, hover: null });

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

// A state change with nothing to ask the worker.
function done(state) {
  return { state, queries: [] };
}

// A state change that also asks the worker something.
function query(state, method, args) {
  const id = state.nextQueryId;
  return {
    state: {
      ...state,
      nextQueryId: id + 1,
      pending: { ...state.pending, [id]: method },
    },
    queries: [{ id, method, args }],
  };
}
