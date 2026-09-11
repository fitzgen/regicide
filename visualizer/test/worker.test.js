import assert from "node:assert/strict";
import test from "node:test";

// The worker installs its handler on `self` at import time, so the fake has to
// be in place first.
const posted = [];
globalThis.self = { postMessage: (m) => posted.push(m) };

const { dispatch } = await import("../js/worker.js");

const BLOB = JSON.stringify({
  version: 1,
  entityKinds: { Val: "v" },
  events: [{ kind: "SpanConstructed", span: 0, val: 0 }],
  index: { byEntity: { Val: { default: [], values: [[0]] } } },
  histograms: [{ id: "spans-per-bundle", title: "Spans per bundle", count: 0 }],
});

test("the worker answers a request through `self`", () => {
  posted.length = 0;
  self.onmessage({ data: { id: 1, method: "load", args: [BLOB] } });
  self.onmessage({ data: { id: 2, method: "histograms", args: [] } });
  assert.deepEqual(posted[0], {
    id: 1,
    result: {
      version: 1,
      entityKinds: { Val: "v" },
      summary: { blocks: 0, insts: 0, events: 1 },
    },
  });
  assert.equal(posted[1].id, 2);
  assert.equal(posted[1].result[0].id, "spans-per-bundle");
});

test("a failing method posts an error rather than dying silently", () => {
  posted.length = 0;
  self.onmessage({ data: { id: 3, method: "nope", args: [] } });
  assert.equal(posted[0].id, 3);
  assert.match(posted[0].error, /no such method/);
  assert.equal(posted[0].result, undefined);
});

test("bad JSON is an error, not a crash", () => {
  const response = dispatch({ id: 4, method: "load", args: ["{"] });
  assert.equal(response.id, 4);
  assert.equal(typeof response.error, "string");
});

test("dispatch is what the main-thread fallback calls", () => {
  // The fallback path has to behave exactly like the worker, or a browser that
  // refuses Blob-URL workers gets a subtly different page.
  dispatch({ id: 5, method: "load", args: [BLOB] });
  assert.deepEqual(dispatch({ id: 6, method: "event", args: [0] }), {
    id: 6,
    result: { kind: "SpanConstructed", span: 0, val: 0 },
  });
});

test("an unsupported version loads no model", () => {
  // The main thread renders the version it got back; what matters here is that
  // nothing downstream of it was built out of a blob nobody understands.
  const response = dispatch({ id: 7, method: "load", args: [JSON.stringify({ version: 99 })] });
  assert.deepEqual(response, { id: 7, result: { version: 99 } });
  assert.match(dispatch({ id: 8, method: "event", args: [0] }).error, /not been loaded/);
});
