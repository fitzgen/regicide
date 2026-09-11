import assert from "node:assert/strict";
import test from "node:test";
import { handleAction } from "../js/actions.js";
import { initialState } from "../js/state.js";

// `Object.freeze` is shallow, and the mistake this guards against — a handler
// stamping a field onto a nested object — hides below the top level.
function deepFreeze(value) {
  if (value === null || typeof value !== "object" || Object.isFrozen(value)) return value;
  Object.freeze(value);
  for (const key of Object.keys(value)) deepFreeze(value[key]);
  return value;
}

// Every action the page has. Commits 08-12 fill in what they do.
const ACTIONS = [
  { type: "selectTab", tab: "events" },
  { type: "clickEntity", ref: { kind: "Val", index: 3 } },
  { type: "clickBreadcrumb", index: 0 },
  { type: "search", query: "Bundle" },
  { type: "queryResult", id: 0, method: "details", result: { fields: [], related: [] } },
  { type: "queryResult", id: 0, method: "searchEvents", result: [1, 2] },
  { type: "queryResult", id: 0, method: "details", error: "boom" },
  { type: "hoverSpan", ref: { kind: "LiveSpan", index: 1 } },
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

test("query ids come from the state, so the handler stays pure", () => {
  const action = { type: "clickEntity", ref: { kind: "Val", index: 3 } };
  const first = handleAction(initialState(), action);
  const second = handleAction(first.state, action);
  assert.deepEqual(first.queries[0], { id: 0, method: "details", args: [action.ref] });
  // The same entity is already selected, so no breadcrumb is pushed, but the
  // query is a fresh one.
  assert.equal(second.queries[0].id, 1);
  assert.deepEqual(second.state.breadcrumbs, [action.ref]);
  assert.deepEqual(second.state.pending, { 0: "details", 1: "details" });
});

test("the two scroll requests are independent", () => {
  // A payload-free `scrolled` would let a histogram scroll clear a function
  // pane request that had not happened yet.
  let state = initialState();
  state = handleAction(state, { type: "clickEntity", ref: { kind: "Val", index: 3 } }).state;
  state = handleAction(state, { type: "clickBreadcrumb", index: 0 }).state;
  state = handleAction(state, { type: "scrollToHistogram", id: "uses-per-span" }).state;
  assert.deepEqual(state.scrollTo, {
    entity: { kind: "Val", index: 3 },
    histogram: "uses-per-span",
  });

  state = handleAction(state, { type: "scrolled", what: "histogram" }).state;
  assert.deepEqual(state.scrollTo, { entity: { kind: "Val", index: 3 }, histogram: null });

  state = handleAction(state, { type: "scrolled", what: "entity" }).state;
  assert.deepEqual(state.scrollTo, { entity: null, histogram: null });
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
  assert.equal(state.details, null);
});
