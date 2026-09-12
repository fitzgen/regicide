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

    // The event index the event log owes a scroll to, as a third field for the
    // same reason. Also one-shot, but cleared a beat later than the other two:
    // the request can outlive a render, because the log may have to be
    // re-searched before the event it names is on screen to scroll to.
    scrollToEvent: null,

    // Details results, keyed by `entityKey(ref)`. A cache, never invalidated.
    details: {},

    // `details`' keys, oldest first, so that the cache can be capped without
    // an insertion-ordered `Map` the state could not be serialized through.
    detailsOrder: [],

    // The key of the details query in flight, which is how the pane tells
    // "not here yet" from "this entity has none".
    pendingDetails: null,

    // The event log tab's query and the event indices it matched. `results`
    // starts `null` rather than empty, so that the pane can tell "no search
    // has answered yet" from "this query matched nothing".
    search: { query: "", results: null, pending: false },

    // Event rows, by event index. The search answers with indices alone -- the
    // log is the one list that can be hundreds of thousands long -- so the
    // rows for the window the list is actually showing are fetched as it
    // scrolls. Never invalidated: an event never changes, and what accumulates
    // here is bounded by what the user scrolled past.
    eventRows: {},

    // The event indices an `eventRows` query is in flight for, as an object
    // rather than a `Set` so that the state stays plain JSON. What stops the
    // render that draws an answer from asking for it again, and why it lives
    // here rather than in the view: a query that fails has to be un-asked, and
    // only the reducer sees the response.
    askedRows: {},

    // The histograms and their grouping for the table of contents, or `null`
    // until the queries the load response starts have answered. Two fields,
    // because they are two answers: the grouping is a list of ids and counts
    // for the contents, and the histograms themselves are what the pane draws.
    histograms: null,
    histogramGroups: null,

    // The function pane, as `model.js` rendered it, or `null` until the load
    // response has come back and the outline query it starts has answered.
    outline: null,

    // The entity the pointer is over, which the details pane prefers over the
    // selection: looking at something should not cost a breadcrumb.
    hovered: null,

    // The bundle of the span the pointer is over. A bundle, not a span: the
    // highlight is bundle-wide, which is also why it cannot be a CSS `:hover`.
    hoveredBundle: null,

    // Queries sent but not yet answered, by id.
    pending: {},

    // The id the next query gets. Kept in the state so that `handleAction`
    // stays a pure function of its inputs.
    nextQueryId: 0,

    // The last error a query came back with, if any.
    error: null,
  };
}
