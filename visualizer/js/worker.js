// Layer 2: the worker wrapper.
//
// The model runs in a web worker so that a search over a large event log
// cannot freeze the UI. This file is the worker's body and stays trivial: it
// receives `{id, method, args}`, calls the model, and posts back `{id, result}`
// or `{id, error}`.
//
// `main.js` posts the blob as *text*: the worker has no DOM and cannot find the
// script tag, and posting a parsed object would structured-clone the whole
// model and leave the main thread holding a second copy.

import { createModel } from "./model.js";

let model = null;

// Handle one request. Exported so that `main.js` can call it directly when
// `new Worker` is not available, and so that a node test can drive it.
export function dispatch(message) {
  const { id, method, args } = message;
  try {
    if (method === "load") {
      const json = JSON.parse(args[0]);
      model = createModel(json);
      // The prefix table goes back to the main thread, which needs it to
      // render labels and would otherwise have to parse the blob itself.
      return { id, result: json.entityKinds || {} };
    }
    if (model === null) throw new Error("the model has not been loaded");
    if (typeof model[method] !== "function") throw new Error("no such method: " + method);
    return { id, result: model[method](...(args || [])) };
  } catch (e) {
    // An error must come back as a value: a worker that throws here just goes
    // quiet, and the pending query never resolves.
    return { id, error: String((e && e.message) || e) };
  }
}

// Only inside an actual worker: on the main thread `self` is the window, whose
// `onmessage` belongs to page messaging. The absence of a document is what
// tells the two apart, and a test's fake `self` looks like the worker.
if (typeof self !== "undefined" &&
    typeof self.postMessage === "function" &&
    typeof self.document === "undefined") {
  self.onmessage = (e) => self.postMessage(dispatch(e.data));
}
