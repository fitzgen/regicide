import assert from "node:assert/strict";
import test from "node:test";
import { createModel } from "../js/model.js";

test("createModel answers the documented queries", () => {
  const model = createModel({});
  for (const method of [
    "details",
    "searchEvents",
    "functionOutline",
    "histograms",
    "event",
    "entity",
  ]) {
    assert.equal(typeof model[method], "function", method);
  }
});

test("a details result carries its own ref back", () => {
  // The main thread caches a result by `entityKey(result.ref)`, so the result
  // has to say which entity it is for; nothing else in it does.
  const ref = { kind: "Val", index: 3 };
  assert.deepEqual(createModel({}).details(ref).ref, ref);
});

test("a SecondaryMap read past the end of `values` is the default", () => {
  // `values` stops at the highest key ever written, so the tail of the entity
  // space is only covered by `default`.
  const model = createModel({
    entityKinds: { Val: "v" },
    index: { byEntity: { Val: { default: [], values: [[0, 2], [1]] } } },
  });
  assert.deepEqual(model.entity({ kind: "Val", index: 0 }).events, [0, 2]);
  assert.deepEqual(model.entity({ kind: "Val", index: 1 }).events, [1]);
  assert.deepEqual(model.entity({ kind: "Val", index: 99 }).events, []);
});

test("a kind with no index of its own reads as no events", () => {
  // `RegUnit` and `RegBank` are entity kinds but nothing indexes them.
  const model = createModel({ entityKinds: { RegUnit: "unit" }, index: { byEntity: {} } });
  assert.deepEqual(model.entity({ kind: "RegUnit", index: 0 }).events, []);
});
