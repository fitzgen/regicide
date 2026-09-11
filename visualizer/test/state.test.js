import assert from "node:assert/strict";
import test from "node:test";
import { initialState } from "../js/state.js";

test("initialState has the documented shape", () => {
  const state = initialState();
  assert.equal(state.tab, "function");
  assert.deepEqual(state.breadcrumbs, []);
  // -1, not 0: `slice(0, 0)` on the first click is what makes the first push
  // work.
  assert.equal(state.activeBreadcrumb, -1);
  assert.equal(state.selected, null);
  assert.deepEqual(state.details, {});
  assert.deepEqual(state.detailsOrder, []);
  assert.equal(state.pendingDetails, null);
  // `null`, not `[]`: "no search has answered yet" and "this query matched
  // nothing" are different things on screen.
  assert.deepEqual(state.search, { query: "", results: null, pending: false });
  assert.deepEqual(state.eventRows, {});
  assert.equal(state.outline, null);
  assert.equal(state.hoveredBundle, null);
  assert.equal(state.scrollToEntity, null);
  assert.equal(state.scrollToHistogram, null);
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
