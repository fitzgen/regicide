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

    // The trail of entity refs the user clicked through on the function tab.
    breadcrumbs: [],

    // Which breadcrumb is active, or -1 when there are none. Not "the last
    // one": walking back up the trail moves this without truncating it, and
    // -1 with an empty list is what makes the first push work.
    activeBreadcrumb: -1,

    // `breadcrumbs[activeBreadcrumb]`. Derived, but stored: the details pane
    // reads it on every render, and a value recomputed from two fields at each
    // read is a value that eventually disagrees with them.
    selected: null,

    // The entity the function pane owes a scroll to. One-shot, cleared by
    // `scrolled`, or every unrelated re-render scrolls the pane out from under
    // the user.
    scrollToEntity: null,

    // The histogram the histograms pane owes a scroll to. A separate field, so
    // that neither scroll can cancel the other's pending request.
    scrollToHistogram: null,

    // Details results, keyed by `entityKey(ref)`. A cache, never invalidated.
    details: {},

    // `details`' keys, oldest first, so that the cache can be capped without
    // an insertion-ordered `Map` the state could not be serialized through.
    detailsOrder: [],

    // The key of the details query in flight, which is how the pane tells
    // "not here yet" from "this entity has none".
    pendingDetails: null,

    // The event log tab.
    search: { query: "", results: [], pending: false },

    // The span the pointer is over, which commit 09 dims the others for.
    hover: null,

    // Queries sent but not yet answered, by id.
    pending: {},

    // The id the next query gets. Kept in the state so that `handleAction`
    // stays a pure function of its inputs.
    nextQueryId: 0,

    // The last error a query came back with, if any.
    error: null,
  };
}
