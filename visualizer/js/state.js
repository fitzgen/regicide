// Layer 3: display state.
//
// The single object describing what is on screen. Pure data and no behavior;
// `actions.js` is what changes it.

// The state the page starts in. JSON-round-trippable, so that it can be logged
// and compared in tests.
export function initialState() {
  return {
    // "function", "events", or "histograms".
    tab: "function",

    // The entity the function tab is showing, and how it was reached. The last
    // breadcrumb is the selection.
    breadcrumbs: [],

    // The details pane's contents, once the query has come back.
    details: null,

    // The event log tab.
    search: { query: "", results: [], pending: false },

    // The span the pointer is over, which commit 09 dims the others for.
    hover: null,

    // Scrolls the view owes us, cleared by a `scrolled` action. The two are
    // independent: a histogram scroll must not clear a pending entity scroll.
    scrollTo: { entity: null, histogram: null },

    // Queries sent but not yet answered, by id.
    pending: {},

    // The id the next query gets. Kept in the state so that `handleAction`
    // stays a pure function of its inputs.
    nextQueryId: 0,

    // The last error a query came back with, if any.
    error: null,
  };
}
