// The glue: the only impure, untested file.
//
// Parses the blob out of the page, starts the worker, owns the current state,
// and runs the loop: action -> handleAction -> render, plus the queries.

import { handleAction } from "./actions.js";
import { install as installEntities } from "./entities.js";
import { initialState } from "./state.js";
import { install as installView, render } from "./view.js";
import { dispatch as dispatchOnMainThread } from "./worker.js";

const json = document.getElementById("regicide-data").textContent;

// The load request predates the state's own query ids, which start at 0.
const LOAD_ID = -1;

let state = initialState();
const methods = new Map();

// A Blob-URL worker is a responsiveness optimization, not a correctness
// requirement: a page opened from `file://` has an opaque origin and some
// browsers refuse to start a worker from it. Falling back to the same dispatch
// function on this thread keeps the page working everywhere, and going through
// `Promise.resolve` keeps the fallback asynchronous so that the two paths
// cannot drift.
let post;
try {
  const source = document.getElementById("regicide-worker").textContent;
  const worker = new Worker(URL.createObjectURL(new Blob([source], { type: "text/javascript" })));
  worker.onmessage = (e) => receive(e.data);
  post = (query) => worker.postMessage(query);
} catch (e) {
  post = (query) => Promise.resolve().then(() => receive(dispatchOnMainThread(query)));
}

function receive(message) {
  if (message.id === LOAD_ID) installEntities(message.result || {});
  dispatch({
    type: "queryResult",
    id: message.id,
    method: methods.get(message.id),
    result: message.result,
    error: message.error,
  });
  methods.delete(message.id);
}

function dispatch(action) {
  const next = handleAction(state, action);
  state = next.state;
  for (const query of next.queries) {
    methods.set(query.id, query.method);
    post(query);
  }
  render(state);
}

methods.set(LOAD_ID, "load");
post({ id: LOAD_ID, method: "load", args: [json] });
installView(document.body, dispatch);
render(state);
