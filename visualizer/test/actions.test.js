import assert from "node:assert/strict";
import test from "node:test";
import { handleAction } from "../js/actions.js";
import { entityKey, sameEntity } from "../js/entities.js";
import { initialState } from "../js/state.js";

// `Object.freeze` is shallow, and the mistake this guards against — a handler
// stamping a field onto a nested object — hides below the top level.
function deepFreeze(value) {
  if (value === null || typeof value !== "object" || Object.isFrozen(value)) return value;
  Object.freeze(value);
  for (const key of Object.keys(value)) deepFreeze(value[key]);
  return value;
}

const V3 = { kind: "Val", index: 3 };
const SPAN0 = { kind: "LiveSpan", index: 0 };
const BLOCK2 = { kind: "Block", index: 2 };
const BUNDLE4 = { kind: "LiveBundle", index: 4 };
const EVENT7 = { kind: "EventIndex", index: 7 };

// The details result for `ref`, in the model's shape.
const details = (ref) => ({ ref, fields: [], eventCount: 0, events: [] });

// Apply a sequence of actions, checking the stored-selection invariant after
// each. Later commits' tests reuse this rather than trusting `selected`.
function run(actions, state = initialState()) {
  let queries = [];
  for (const action of actions) {
    const next = handleAction(deepFreeze(state), deepFreeze(action));
    state = next.state;
    queries = next.queries;
    const active = state.breadcrumbs[state.activeBreadcrumb];
    assert.ok(
      state.selected === null ? active === undefined : sameEntity(state.selected, active),
      "`selected` drifted from `breadcrumbs[activeBreadcrumb]` after " + action.type,
    );
  }
  return { state, queries };
}

// Every action the page has. Commits 09-12 fill in what they do.
const ACTIONS = [
  { type: "loaded" },
  { type: "selectTab", tab: "events" },
  { type: "clickEntity", ref: V3 },
  { type: "clickBreadcrumb", index: 0 },
  { type: "search", query: "Bundle" },
  { type: "queryResult", id: 0, method: "details", result: details(V3) },
  { type: "queryResult", id: 0, method: "searchEvents", args: [""], result: [1, 2] },
  { type: "queryResult", id: 0, method: "eventRows", result: [{ index: 1, kind: "X", summary: [] }] },
  { type: "needEventRows", indices: [1, 2] },
  { type: "clickEntityFromEvent", entity: V3 },
  { type: "queryResult", id: 0, method: "functionOutline", result: { lines: [], bars: [] } },
  { type: "queryResult", id: 0, method: "details", error: "boom" },
  { type: "hoverEntity", ref: SPAN0 },
  { type: "unhoverEntity" },
  { type: "scrollToHistogram", id: "spans-per-bundle" },
  { type: "queryResult", id: 0, method: "histograms", result: [] },
  { type: "queryResult", id: 0, method: "histogramGroups", result: [] },
  { type: "scrolled", what: "entity" },
  { type: "scrolled", what: "histogram" },
  { type: "clickEntity", ref: EVENT7 },
  { type: "scrolled", what: "event" },
  { type: "queryResult", id: 0, method: "details", args: [EVENT7], result: null },
];

test("handleAction returns {state, queries} and mutates neither input", () => {
  for (const action of ACTIONS) {
    // Freeze the action too: stamping an id or a timestamp onto it is a real
    // and easy mistake, and freezing only the state does not catch it.
    const state = deepFreeze(initialState());
    const result = handleAction(state, deepFreeze(action));
    assert.ok(result.state && typeof result.state === "object", action.type);
    assert.ok(Array.isArray(result.queries), action.type);
    for (const query of result.queries) {
      assert.equal(typeof query.id, "number");
      assert.equal(typeof query.method, "string");
      assert.ok(Array.isArray(query.args));
    }
  }
});

test("an unknown action is a no-op", () => {
  const state = initialState();
  assert.deepEqual(handleAction(state, { type: "nope" }), { state, queries: [] });
});

test("clicking an entity truncates everything after the active breadcrumb", () => {
  // The spec's example: `[span0, v3, bundle4]` active at `v3`, click `block2`.
  const { state } = run([
    { type: "clickEntity", ref: SPAN0 },
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: BUNDLE4 },
    { type: "clickBreadcrumb", index: 1 },
    { type: "clickEntity", ref: BLOCK2 },
  ]);
  assert.deepEqual(state.breadcrumbs, [SPAN0, V3, BLOCK2]);
  assert.equal(state.activeBreadcrumb, 2);
  assert.deepEqual(state.selected, BLOCK2);
});

test("clicking a breadcrumb moves the active index without truncating", () => {
  const { state } = run([
    { type: "clickEntity", ref: SPAN0 },
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: BUNDLE4 },
    { type: "clickBreadcrumb", index: 0 },
  ]);
  assert.deepEqual(state.breadcrumbs, [SPAN0, V3, BUNDLE4]);
  assert.equal(state.activeBreadcrumb, 0);
  assert.deepEqual(state.selected, SPAN0);
  assert.deepEqual(state.scrollToEntity, SPAN0);
});

test("clicking the active entity does not push a duplicate", () => {
  // A fresh ref rather than `V3` itself, because the guard is structural:
  // two refs for the same entity are never `===`.
  const { state, queries } = run([
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: { ...V3 } },
  ]);
  assert.deepEqual(state.breadcrumbs, [V3]);
  assert.equal(state.activeBreadcrumb, 0);
  assert.ok(sameEntity(state.selected, V3));
  // Still a re-select, so the pane is still asked to scroll back to it.
  assert.deepEqual(state.scrollToEntity, V3);
  assert.deepEqual(
    queries.map((q) => q.method),
    ["details"],
  );
});

test("clicking a non-active earlier breadcrumb still truncates and pushes", () => {
  // Only the *active* crumb is deduplicated: walking back to `span0` and
  // clicking it again is a click on something that is already selected, but
  // clicking `v3` from there is a new step and drops `bundle4`.
  const { state } = run([
    { type: "clickEntity", ref: SPAN0 },
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: BUNDLE4 },
    { type: "clickBreadcrumb", index: 0 },
    { type: "clickEntity", ref: { ...V3 } },
  ]);
  assert.deepEqual(state.breadcrumbs, [SPAN0, V3]);
  assert.equal(state.activeBreadcrumb, 1);
});

test("an out-of-range breadcrumb index is a no-op", () => {
  const { state } = run([{ type: "clickEntity", ref: V3 }]);
  for (const index of [-1, 1, 99]) {
    assert.deepEqual(handleAction(state, { type: "clickBreadcrumb", index }), {
      state,
      queries: [],
    });
  }
});

test("selectTab preserves the rest of the state", () => {
  const { state } = run([
    { type: "clickEntity", ref: V3 },
    { type: "selectTab", tab: "events" },
  ]);
  assert.equal(state.tab, "events");
  assert.deepEqual(state.breadcrumbs, [V3]);
  assert.equal(state.activeBreadcrumb, 0);
});

test("query ids come from the state, so the handler stays pure", () => {
  const action = { type: "clickEntity", ref: V3 };
  const first = handleAction(initialState(), action);
  const second = handleAction(first.state, action);
  assert.deepEqual(first.queries[0], { id: 0, method: "details", args: [V3] });
  assert.equal(second.queries[0].id, 1);
  assert.deepEqual(second.state.pending, { 0: "details", 1: "details" });
});

test("out-of-order details results are both cached, and the pane reads the selected one", () => {
  // A late result is not stale: it is a warm cache entry for a breadcrumb the
  // user is one click from returning to.
  let { state } = run([
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: BLOCK2 },
  ]);
  state = run(
    [
      { type: "queryResult", id: 1, method: "details", result: details(BLOCK2) },
      { type: "queryResult", id: 0, method: "details", result: details(V3) },
    ],
    state,
  ).state;

  assert.deepEqual(Object.keys(state.details).sort(), ["Block:2", "Val:3"]);
  assert.deepEqual(state.details[entityKey(state.selected)].ref, BLOCK2);
});

test("pendingDetails is cleared by the matching result only", () => {
  let { state } = run([{ type: "clickEntity", ref: V3 }]);
  assert.equal(state.pendingDetails, "Val:3");

  state = run([{ type: "clickEntity", ref: BLOCK2 }], state).state;
  assert.equal(state.pendingDetails, "Block:2");

  // The first click's answer, arriving after the second click.
  state = run([{ type: "queryResult", id: 0, method: "details", result: details(V3) }], state).state;
  assert.equal(state.pendingDetails, "Block:2");

  state = run(
    [{ type: "queryResult", id: 1, method: "details", result: details(BLOCK2) }],
    state,
  ).state;
  assert.equal(state.pendingDetails, null);
});

test("a result for another method leaves the details cache alone", () => {
  const { state } = run([
    { type: "clickEntity", ref: V3 },
    { type: "queryResult", id: 0, method: "searchEvents", result: [4, 5] },
  ]);
  assert.deepEqual(state.details, {});
  assert.equal(state.pendingDetails, "Val:3");
});

test("the details cache evicts its oldest entry", () => {
  let state = initialState();
  for (let i = 0; i <= 50; i++) {
    state = run(
      [{ type: "queryResult", id: i, method: "details", result: details({ kind: "Val", index: i }) }],
      state,
    ).state;
  }
  assert.equal(Object.keys(state.details).length, 50);
  assert.equal(state.details["Val:0"], undefined);
  assert.ok(state.details["Val:50"]);
});

test("the two scroll requests are independent", () => {
  // A payload-free `scrolled` would let a histogram scroll clear a function
  // pane request that had not been served yet.
  let { state } = run([
    { type: "clickEntity", ref: V3 },
    { type: "scrollToHistogram", id: "uses-per-span" },
  ]);
  assert.deepEqual(state.scrollToEntity, V3);
  assert.equal(state.scrollToHistogram, "uses-per-span");

  state = run([{ type: "scrolled", what: "nonsense" }], state).state;
  assert.deepEqual(state.scrollToEntity, V3);
  assert.equal(state.scrollToHistogram, "uses-per-span");

  state = run([{ type: "scrolled", what: "histogram" }], state).state;
  assert.deepEqual(state.scrollToEntity, V3);
  assert.equal(state.scrollToHistogram, null);

  state = run([{ type: "scrolled", what: "entity" }], state).state;
  assert.equal(state.scrollToEntity, null);
});

test("a query result clears its pending entry", () => {
  const { state, queries } = handleAction(initialState(), { type: "search", query: "Bundle" });
  assert.deepEqual(state.pending, { 0: "searchEvents" });
  const next = handleAction(state, {
    type: "queryResult",
    id: queries[0].id,
    method: "searchEvents",
    args: queries[0].args,
    result: [4, 5],
  }).state;
  assert.deepEqual(next.pending, {});
  assert.deepEqual(next.search, { query: "Bundle", results: [4, 5], pending: false });
});

test("an error comes back as state, not as a throw", () => {
  const state = handleAction(initialState(), {
    type: "queryResult",
    id: 0,
    method: "details",
    error: "boom",
  }).state;
  assert.equal(state.error, "boom");
  assert.deepEqual(state.details, {});
});

test("hovering a span highlights its whole bundle", () => {
  // The view knows which bar the pointer is over; which bundle that bar
  // belongs to is the outline's business, so the action carries only the span.
  const outline = {
    lines: [],
    bars: [
      { span: SPAN0, bundle: BUNDLE4 },
      { span: { kind: "LiveSpan", index: 1 }, bundle: null },
    ],
  };
  const loaded = { ...initialState(), outline };

  const hovered = run([{ type: "hoverEntity", ref: { ...SPAN0 } }], loaded).state;
  assert.deepEqual(hovered.hoveredBundle, BUNDLE4, "a fresh ref for the same span missed");

  assert.equal(run([{ type: "unhoverEntity" }], hovered).state.hoveredBundle, null);

  // A span that reached no bundle, and a span with no bar at all, both leave
  // nothing highlighted rather than throwing. So does an entity that is not a
  // span, which is now hoverable too.
  for (const ref of [{ kind: "LiveSpan", index: 1 }, { kind: "LiveSpan", index: 99 }, BLOCK2]) {
    const state = run([{ type: "hoverEntity", ref }], loaded).state;
    assert.equal(state.hoveredBundle, null, entityKey(ref));
  }
  assert.equal(run([{ type: "hoverEntity", ref: SPAN0 }]).state.hoveredBundle, null, "no outline");
});

test("hovering an entity previews it without touching the trail", () => {
  // Hovering is looking; the trail is a record of where the user chose to go.
  const before = run([{ type: "clickEntity", ref: V3 }]).state;
  const { state, queries } = run([{ type: "hoverEntity", ref: BLOCK2 }], before);

  assert.deepEqual(state.hovered, BLOCK2);
  assert.deepEqual(state.breadcrumbs, before.breadcrumbs);
  assert.equal(state.activeBreadcrumb, before.activeBreadcrumb);
  assert.equal(state.scrollToEntity, before.scrollToEntity);

  // The pane needs the fields, and says so while they are on their way.
  assert.deepEqual(
    queries.map((q) => [q.method, q.args]),
    [["details", [BLOCK2]]],
  );
  assert.equal(state.pendingDetails, entityKey(BLOCK2));

  // Dropping the hover is what puts the selection back in the pane.
  const after = run([{ type: "unhoverEntity" }], state).state;
  assert.equal(after.hovered, null);
  assert.deepEqual(after.selected, V3);
});

test("hovering something already cached asks for nothing", () => {
  // The pointer crosses a lot of entities on its way somewhere.
  const cached = run([
    { type: "clickEntity", ref: BLOCK2 },
    { type: "queryResult", id: 0, method: "details", result: details(BLOCK2) },
    { type: "clickEntity", ref: V3 },
    { type: "queryResult", id: 1, method: "details", result: details(V3) },
  ]).state;

  const { state, queries } = run([{ type: "hoverEntity", ref: { ...BLOCK2 } }], cached);
  assert.deepEqual(queries, []);
  assert.deepEqual(state.hovered, BLOCK2);
  // And nothing is left pending, which is what the pane's "Loading…" reads.
  assert.equal(state.pendingDetails, null);
});

test("the outline arrives once the blob has loaded", () => {
  // The load response is not a query result, so `loaded` is what starts the
  // page: nothing else would ever ask for the function pane.
  const first = run([{ type: "loaded" }]);
  // The empty search rides along: it is the whole log, and it is what the
  // event tab opens on. So do the histograms, which are already computed.
  assert.deepEqual(first.queries, [
    { id: 0, method: "functionOutline", args: [] },
    { id: 1, method: "searchEvents", args: [""] },
    { id: 2, method: "histograms", args: [] },
    { id: 3, method: "histogramGroups", args: [] },
  ]);
  assert.equal(first.state.outline, null, "the outline was invented before it arrived");

  const outline = { lines: [], bars: [] };
  const done = run(
    [{ type: "queryResult", id: 0, method: "functionOutline", result: outline }],
    first.state,
  ).state;
  assert.equal(done.outline, outline);
  // Everything it went out with is still in flight.
  assert.deepEqual(done.pending, {
    1: "searchEvents",
    2: "histograms",
    3: "histogramGroups",
  });
});

test("clicking an entity in the function pane walks the breadcrumbs", () => {
  // The function pane's click is commit 08's `clickEntity`, unchanged: a span
  // bar and a value in a line go through the same handler.
  const { state, queries } = run([
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: SPAN0 },
  ]);
  assert.deepEqual(state.breadcrumbs, [V3, SPAN0]);
  assert.equal(state.activeBreadcrumb, 1);
  assert.deepEqual(state.scrollToEntity, SPAN0);
  assert.equal(state.pendingDetails, entityKey(SPAN0));
  assert.deepEqual(queries, [{ id: 1, method: "details", args: [SPAN0] }]);
});

test("clicking an entity in the details pane walks the trail like any other click", () => {
  // The details pane's listener dispatches the same `clickEntity`, so a
  // reference followed from a field truncates the trail, pushes, selects, and
  // -- the part that only matters from this pane -- scrolls the function pane
  // to what was clicked.
  let { state } = run([
    { type: "clickEntity", ref: SPAN0 },
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: BUNDLE4 },
    { type: "clickBreadcrumb", index: 1 },
  ]);
  const { state: next, queries } = run([{ type: "clickEntity", ref: BLOCK2 }], state);
  assert.deepEqual(next.breadcrumbs, [SPAN0, V3, BLOCK2]);
  assert.equal(next.activeBreadcrumb, 2);
  assert.deepEqual(next.selected, BLOCK2);
  assert.deepEqual(next.scrollToEntity, BLOCK2);
  // Four queries preceded it -- three clicks and the breadcrumb -- and ids
  // come from the state, so this one is the fifth.
  assert.deepEqual(queries, [{ id: 4, method: "details", args: [BLOCK2] }]);
});

test("an entity with no cached details is pending until its result arrives", () => {
  // The pane's three display states hang off this: a cache hit renders, a
  // pending flag renders "Loading…", and neither renders an empty pane.
  const { state, queries } = run([{ type: "clickEntity", ref: V3 }]);
  const key = entityKey(V3);
  assert.equal(state.details[key], undefined);
  assert.equal(state.pendingDetails, key);

  const result = details(V3);
  const arrived = run(
    [{ type: "queryResult", id: queries[0].id, method: "details", result }],
    state,
  ).state;
  assert.equal(arrived.pendingDetails, null);
  assert.equal(arrived.details[key], result);

  // And a failed query leaves neither, which is the empty-pane case. The
  // pending key has to go with it: the pane would otherwise read "Loading..."
  // for the rest of the session, since coming back to the entity is answered
  // out of the cache and there is nothing in it.
  const failed = run(
    [{ type: "queryResult", id: queries[0].id, method: "details", args: [V3], error: "boom" }],
    state,
  ).state;
  assert.equal(failed.details[key], undefined);
  assert.equal(failed.pendingDetails, null);
  assert.equal(failed.error, "boom");
});

test("a failed query clears only its own pending mark", () => {
  // Two details queries in flight, the first failing. The pane is waiting on
  // the second, and an error on the first must not make it say the entity has
  // no details.
  const first = run([{ type: "clickEntity", ref: V3 }]);
  const second = run([{ type: "clickEntity", ref: BLOCK2 }], first.state);
  const key = entityKey(BLOCK2);
  assert.equal(second.state.pendingDetails, key);

  const after = run(
    [{ type: "queryResult", id: first.queries[0].id, method: "details", args: [V3], error: "boom" }],
    second.state,
  ).state;
  assert.equal(after.pendingDetails, key);
});

test("a failed search stops the spinner and keeps what was on screen", () => {
  const { state, queries } = run([
    { type: "search", query: "Spill" },
  ]);
  const shown = run(
    [{ type: "queryResult", id: queries[0].id, method: "searchEvents", args: ["Spill"], result: [7] }],
    state,
  ).state;

  const again = run([{ type: "search", query: "Spilled" }], shown);
  assert.equal(again.state.search.pending, true);

  const failed = run(
    [{
      type: "queryResult",
      id: again.queries[0].id,
      method: "searchEvents",
      args: ["Spilled"],
      error: "boom",
    }],
    again.state,
  ).state;
  assert.equal(failed.search.pending, false, "the event list kept spinning");
  assert.equal(failed.error, "boom");
  // Stale rows under an error banner beat an empty list.
  assert.deepEqual(failed.search.results, [7]);
});

test("a search marks itself pending and asks once", () => {
  const { state, queries } = run([{ type: "search", query: "Spill" }]);
  assert.deepEqual(state.search, { query: "Spill", results: null, pending: true });
  assert.deepEqual(queries, [{ id: 0, method: "searchEvents", args: ["Spill"] }]);
});

test("a search result for abandoned text is dropped, and the current one kept", () => {
  // Out-of-order responses are guaranteed: the glue debounces, so two queries
  // can be in flight, and the worker answers a cheap query first. The text
  // the result answered comes back with it, which is what makes this a string
  // compare rather than a guess.
  const { state } = run([{ type: "search", query: "Sp" }, { type: "search", query: "Spill" }]);

  const stale = run(
    [{ type: "queryResult", id: 0, method: "searchEvents", args: ["Sp"], result: [1, 2, 3] }],
    state,
  ).state;
  assert.equal(stale.search.results, null, "a result for abandoned text was shown");
  assert.equal(stale.search.pending, true, "the query still in flight was forgotten");
  // The pending entry still clears: the query is answered either way.
  assert.deepEqual(stale.pending, { 1: "searchEvents" });

  const fresh = run(
    [{ type: "queryResult", id: 1, method: "searchEvents", args: ["Spill"], result: [7] }],
    stale,
  ).state;
  assert.deepEqual(fresh.search, { query: "Spill", results: [7], pending: false });
});

test("event rows are asked for once and kept by index", () => {
  // The list is virtualized, so it asks for the window it is about to draw.
  // Whatever it already has is not asked for again, which is what keeps a
  // scroll from re-requesting the screen it is sitting on.
  const first = run([{ type: "needEventRows", indices: [4, 5] }]);
  assert.deepEqual(first.queries, [{ id: 0, method: "eventRows", args: [[4, 5]] }]);

  const rows = [
    { index: 4, kind: "SpillPlaced", summary: [] },
    { index: 5, kind: "SpillPlaced", summary: [] },
  ];
  const { state } = run(
    [{ type: "queryResult", id: 0, method: "eventRows", args: [[4, 5]], result: rows }],
    first.state,
  );
  assert.deepEqual(Object.keys(state.eventRows), ["4", "5"]);
  assert.equal(state.eventRows[5], rows[1]);

  // Overlapping windows ask only for the part that is new.
  assert.deepEqual(run([{ type: "needEventRows", indices: [5, 6] }], state).queries, [
    { id: 1, method: "eventRows", args: [[6]] },
  ]);
  assert.deepEqual(run([{ type: "needEventRows", indices: [4, 5] }], state).queries, []);
});

test("a query in flight is not asked for twice, and a failed one is re-asked", () => {
  // The view asks for the window it is about to draw on every render, so the
  // indices already in flight have to be remembered somewhere -- and un-asked
  // when the query fails, or those rows read "..." for the life of the page.
  const first = run([{ type: "needEventRows", indices: [4, 5] }]);
  assert.deepEqual(first.state.askedRows, { 4: true, 5: true });
  assert.deepEqual(run([{ type: "needEventRows", indices: [4, 5] }], first.state).queries, []);

  const failed = run(
    [{ type: "queryResult", id: 0, method: "eventRows", args: [[4, 5]], error: "boom" }],
    first.state,
  ).state;
  assert.deepEqual(failed.askedRows, {});
  assert.equal(failed.error, "boom");
  assert.deepEqual(run([{ type: "needEventRows", indices: [4, 5] }], failed).queries, [
    { id: 1, method: "eventRows", args: [[4, 5]] },
  ]);
});

test("an answered query stops being in flight without being re-asked", () => {
  // Both halves matter: the indices leave `askedRows`, and `eventRows` is what
  // keeps them from being asked for again.
  const first = run([{ type: "needEventRows", indices: [4] }]);
  const rows = [{ index: 4, kind: "SpillPlaced", summary: [] }];
  const { state } = run(
    [{ type: "queryResult", id: 0, method: "eventRows", args: [[4]], result: rows }],
    first.state,
  );
  assert.deepEqual(state.askedRows, {});
  assert.deepEqual(run([{ type: "needEventRows", indices: [4] }], state).queries, []);
});

test("clicking an entity in an event row is a function-pane click with a tab switch", () => {
  // Two things in order: leave the log, then do exactly what a click in the
  // function pane does. The second half is the existing handler, so the
  // breadcrumb trail, the selection and the scroll cannot drift apart from
  // it -- which is what this asserts.
  const before = run([{ type: "selectTab", tab: "events" }, { type: "clickEntity", ref: SPAN0 }]).state;

  const viaEvent = run([{ type: "clickEntityFromEvent", entity: BLOCK2 }], before);
  const viaPane = run([{ type: "clickEntity", ref: BLOCK2 }], before);

  assert.equal(viaEvent.state.tab, "function", "the log was still on screen");
  assert.equal(viaPane.state.tab, "events", "a plain click moved the tab");
  assert.deepEqual({ ...viaEvent.state, tab: null }, { ...viaPane.state, tab: null });
  assert.deepEqual(viaEvent.queries, viaPane.queries);
});

test("the histograms arrive as two separate answers", () => {
  const histograms = [{ id: "spans-per-value", title: "Spans per value", count: 2, buckets: [] }];
  const groups = [{ group: "Liveness", items: [{ id: "spans-per-value", title: "x", count: 2 }] }];
  let { state } = run([{ type: "loaded" }]);
  assert.equal(state.histograms, null);
  assert.equal(state.histogramGroups, null);

  state = run(
    [
      { type: "queryResult", id: 2, method: "histograms", result: histograms },
      { type: "queryResult", id: 3, method: "histogramGroups", result: groups },
    ],
    state,
  ).state;
  assert.equal(state.histograms, histograms);
  assert.equal(state.histogramGroups, groups);
  assert.deepEqual(state.pending, { 0: "functionOutline", 1: "searchEvents" });
});

test("a histogram scroll survives a tab switch", () => {
  // The field belongs to the histograms tab, and the gesture that asks for the
  // scroll is often the same one that selects the tab: clearing it on a switch
  // would drop the request that the switch was made for.
  let { state } = run([
    { type: "scrollToHistogram", id: "spills-per-value" },
    { type: "selectTab", tab: "histograms" },
  ]);
  assert.equal(state.scrollToHistogram, "spills-per-value");

  state = run([{ type: "selectTab", tab: "function" }], state).state;
  assert.equal(state.scrollToHistogram, "spills-per-value");
});

test("a later histogram scroll replaces the pending one", () => {
  // Two clicks in the table of contents before the first has been served: the
  // second is where the user wants to be, and serving both would scroll past
  // it to get there.
  const { state } = run([
    { type: "scrollToHistogram", id: "spills-per-value" },
    { type: "scrollToHistogram", id: "uses-per-span" },
  ]);
  assert.equal(state.scrollToHistogram, "uses-per-span");
});

test("clicking an event goes to the log and keeps a filter that shows it", () => {
  // The user searched for something, found an event in a details pane's list,
  // and clicked it. The filter they typed is the context they are reading in,
  // so it stays; the scroll happens within it.
  let { state } = run([
    { type: "search", query: "Bundle" },
    { type: "queryResult", id: 1, method: "searchEvents", args: ["Bundle"], result: [4, 7, 9] },
    { type: "clickEntity", ref: V3 },
  ]);
  const before = state;

  const { state: after, queries } = run([{ type: "clickEntity", ref: EVENT7 }], state);
  assert.equal(after.tab, "events");
  assert.equal(after.scrollToEvent, 7);
  assert.deepEqual(queries, []);
  assert.equal(after.search.query, "Bundle");
  assert.deepEqual(after.search.results, [4, 7, 9]);

  // An event is not an entity: none of the selection state moves.
  assert.deepEqual(after.breadcrumbs, before.breadcrumbs);
  assert.equal(after.activeBreadcrumb, before.activeBreadcrumb);
  assert.deepEqual(after.selected, before.selected);
  assert.deepEqual(after.scrollToEntity, before.scrollToEntity);
});

test("clicking an event the filter hides clears the query", () => {
  // Otherwise the click is a no-op: the list draws the results and nothing
  // else, so an event outside them has nowhere to be scrolled to.
  let { state } = run([
    { type: "search", query: "Spill" },
    { type: "queryResult", id: 1, method: "searchEvents", args: ["Spill"], result: [4, 9] },
  ]);

  const { state: after, queries } = run([{ type: "clickEntity", ref: EVENT7 }], state);
  assert.equal(after.tab, "events");
  assert.equal(after.scrollToEvent, 7);
  assert.equal(after.search.query, "");
  assert.equal(after.search.pending, true);
  assert.equal(queries.length, 1);
  assert.equal(queries[0].method, "searchEvents");
  assert.deepEqual(queries[0].args, [""]);
});

test("an event scroll is one-shot", () => {
  let { state } = run([
    { type: "queryResult", id: 1, method: "searchEvents", args: [""], result: [7] },
    { type: "clickEntity", ref: EVENT7 },
  ]);
  assert.equal(state.scrollToEvent, 7);

  // And the other two requests are not the one being cleared.
  state = run([{ type: "scrolled", what: "entity" }], state).state;
  assert.equal(state.scrollToEvent, 7);
  state = run([{ type: "scrolled", what: "event" }], state).state;
  assert.equal(state.scrollToEvent, null);
});

test("a details result of null clears its pending key", () => {
  // What the crash was: a ref the model has no pane for answers `null`, and
  // reading `.ref` off it threw. The pane has to stop saying "Loading..."
  // either way.
  let { state } = run([{ type: "hoverEntity", ref: SPAN0 }]);
  assert.equal(state.pendingDetails, entityKey(SPAN0));

  state = run(
    [{ type: "queryResult", id: 1, method: "details", args: [SPAN0], result: null }],
    state,
  ).state;
  assert.equal(state.pendingDetails, null);
  assert.deepEqual(state.details, {});
  assert.equal(state.error, null);
});

test("a null details result for another entity leaves the pending key alone", () => {
  // Two queries in flight and the uninteresting one comes back empty: the
  // pane is still waiting on the one the user is looking at.
  let { state } = run([{ type: "hoverEntity", ref: SPAN0 }]);
  state = run(
    [{ type: "queryResult", id: 9, method: "details", args: [BUNDLE4], result: null }],
    state,
  ).state;
  assert.equal(state.pendingDetails, entityKey(SPAN0));
});
