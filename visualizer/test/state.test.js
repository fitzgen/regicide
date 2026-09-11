import assert from "node:assert/strict";
import test from "node:test";
import { initialState } from "../js/state.js";

test("initialState has the documented shape", () => {
  const state = initialState();
  assert.equal(state.tab, "function");
  assert.deepEqual(state.breadcrumbs, []);
  assert.equal(state.details, null);
  assert.deepEqual(state.search, { query: "", results: [], pending: false });
  assert.equal(state.hover, null);
  assert.deepEqual(state.scrollTo, { entity: null, histogram: null });
  assert.deepEqual(state.pending, {});
  assert.equal(state.nextQueryId, 0);
  assert.equal(state.error, null);
});

test("initialState is fresh each time", () => {
  const a = initialState();
  a.breadcrumbs.push({ kind: "Val", index: 0 });
  assert.deepEqual(initialState().breadcrumbs, []);
});

test("the state is plain JSON", () => {
  const state = initialState();
  assert.deepEqual(JSON.parse(JSON.stringify(state)), state);
});
