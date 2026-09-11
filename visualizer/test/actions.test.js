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
  { type: "hoverSpan", ref: SPAN0 },
  { type: "unhoverSpan" },
  { type: "scrollToHistogram", id: "spans-per-bundle" },
  { type: "scrolled", what: "entity" },
  { type: "scrolled", what: "histogram" },
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

test("clicking the active entity pushes a duplicate", () => {
  // The rule says push, and a `[v3, v3]` trail is honest about what the user
  // did. `sameEntity`, because two structurally equal refs are never `===`.
  const { state } = run([
    { type: "clickEntity", ref: V3 },
    { type: "clickEntity", ref: { ...V3 } },
  ]);
  assert.equal(state.breadcrumbs.length, 2);
  assert.ok(sameEntity(state.breadcrumbs[0], state.breadcrumbs[1]));
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

  const hovered = run([{ type: "hoverSpan", ref: { ...SPAN0 } }], loaded).state;
  assert.deepEqual(hovered.hoveredBundle, BUNDLE4, "a fresh ref for the same span missed");

  assert.equal(run([{ type: "unhoverSpan" }], hovered).state.hoveredBundle, null);

  // A span that reached no bundle, and a span with no bar at all, both leave
  // nothing highlighted rather than throwing.
  for (const index of [1, 99]) {
    const ref = { kind: "LiveSpan", index };
    assert.equal(run([{ type: "hoverSpan", ref }], loaded).state.hoveredBundle, null, "span" + index);
  }
  assert.equal(run([{ type: "hoverSpan", ref: SPAN0 }]).state.hoveredBundle, null, "no outline");
});

test("the outline arrives once the blob has loaded", () => {
  // The load response is not a query result, so `loaded` is what starts the
  // page: nothing else would ever ask for the function pane.
  const first = run([{ type: "loaded" }]);
  // The empty search rides along: it is the whole log, and it is what the
  // event tab opens on.
  assert.deepEqual(first.queries, [
    { id: 0, method: "functionOutline", args: [] },
    { id: 1, method: "searchEvents", args: [""] },
  ]);
  assert.equal(first.state.outline, null, "the outline was invented before it arrived");

  const outline = { lines: [], bars: [] };
  const done = run(
    [{ type: "queryResult", id: 0, method: "functionOutline", result: outline }],
    first.state,
  ).state;
  assert.equal(done.outline, outline);
  // The search it went out with is still in flight.
  assert.deepEqual(done.pending, { 1: "searchEvents" });
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

  // And a failed query leaves neither, which is the empty-pane case.
  const failed = run(
    [{ type: "queryResult", id: queries[0].id, method: "details", error: "boom" }],
    state,
  ).state;
  assert.equal(failed.details[key], undefined);
  assert.equal(failed.pendingDetails, key);
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
    [{ type: "queryResult", id: 0, method: "eventRows", result: rows }],
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
