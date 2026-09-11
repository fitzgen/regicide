// Layer 4: actions and handlers.
//
// `handleAction` is the only place in the page that decides anything. It is
// pure: same input, same output, no DOM, no worker, and neither argument is
// mutated. `queries` is what the glue posts to the worker; a response comes
// back in as another action.

import { sameEntity } from "./entities.js";

// Apply `action` to `state`.
//
// Returns the next state and the queries the glue should send. A query's
// `method` is echoed back with its result, because one `queryResult` action
// carries responses for every query kind and dispatching on the shape of the
// result would be guesswork.
export function handleAction(state, action) {
  switch (action.type) {
    case "selectTab":
      return done({ ...state, tab: action.tab });

    case "clickEntity": {
      const breadcrumbs = sameEntity(last(state.breadcrumbs), action.ref)
        ? state.breadcrumbs
        : [...state.breadcrumbs, action.ref];
      return query({ ...state, breadcrumbs, details: null }, "details", [action.ref]);
    }

    case "clickBreadcrumb": {
      const breadcrumbs = state.breadcrumbs.slice(0, action.index + 1);
      const ref = last(breadcrumbs);
      const next = {
        ...state,
        breadcrumbs,
        details: null,
        scrollTo: { ...state.scrollTo, entity: ref },
      };
      return ref === null ? done(next) : query(next, "details", [ref]);
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
          return done({ ...next, details: action.result });
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
      return done({ ...state, scrollTo: { ...state.scrollTo, histogram: action.id } });

    case "scrolled":
      return done({ ...state, scrollTo: { ...state.scrollTo, [action.what]: null } });

    default:
      return done(state);
  }
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

// The current selection, or `null` when nothing is selected.
function last(list) {
  return list.length === 0 ? null : list[list.length - 1];
}
