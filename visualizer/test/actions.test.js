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

// The details result for `ref`, in commit 10's shape.
const details = (ref) => ({ ref, fields: [], events: [] });

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
  { type: "selectTab", tab: "events" },
  { type: "clickEntity", ref: V3 },
  { type: "clickBreadcrumb", index: 0 },
  { type: "search", query: "Bundle" },
  { type: "queryResult", id: 0, method: "details", result: details(V3) },
  { type: "queryResult", id: 0, method: "searchEvents", result: [1, 2] },
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
