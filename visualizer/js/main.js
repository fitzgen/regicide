// The glue: the only impure, untested file.
//
// Parses the blob out of the page, starts the worker, owns the current state,
// and runs the loop: action -> handleAction -> render, plus the queries.

import { handleAction } from "./actions.js";
import { installEntities } from "./entities.js";
import { initialState } from "./state.js";
import { installView, render } from "./view.js";

const json = document.getElementById("regicide-data").textContent;
const workerSource = document.getElementById("regicide-worker").textContent;
const summary = document.getElementById("summary");

// The load request predates the state's own query ids, which start at 0.
const LOAD_ID = -1;

// The blob format this page understands. The worker does the comparing, since
// it is the only side that parses; this is here for the message.
const VERSION = 1;

// How long the search waits for the typing to stop. A keystroke per query
// over a large log is the exact thing the worker was introduced to avoid: the
// UI would stay responsive, but every scan would still queue behind the last.
// It lives here rather than in `handleAction` so that the handler stays pure
// and synchronous.
const SEARCH_DEBOUNCE_MS = 30;

let state = initialState();

// Queries sent but not answered, by id. The whole query, not just its method:
// a search result is only useful if the text it answered comes back with it.
const sent = new Map();

// A Blob-URL worker is a responsiveness optimization, not a correctness
// requirement: a page opened from `file://` has an opaque origin and some
// browsers refuse to start a worker from it. Falling back to the same dispatch
// function on this thread keeps the page working everywhere, and going through
// `Promise.resolve` keeps the fallback asynchronous so that the two paths
// cannot drift.
//
// The fallback evaluates the worker's own source rather than importing it:
// `model.js` is deliberately not part of this script, so there is nothing here
// to import, and evaluating the same text is what keeps the two paths the same
// code.
let post;
try {
  const url = URL.createObjectURL(new Blob([workerSource], { type: "text/javascript" }));
  const worker = new Worker(url);
  worker.onmessage = (e) => receive(e.data);
  post = (query) => worker.postMessage(query);
} catch (e) {
  const dispatchHere = new Function(workerSource + "\nreturn dispatch;")();
  post = (query) => Promise.resolve().then(() => receive(dispatchHere(query)));
}

function receive(message) {
  if (message.id === LOAD_ID) return loaded(message);
  const query = sent.get(message.id) || {};
  sent.delete(message.id);
  dispatch({
    type: "queryResult",
    id: message.id,
    method: query.method,
    args: query.args,
    result: message.result,
    error: message.error,
  });
}

// The load response, which is not a query result: it settles whether the page
// can show anything at all, and carries the prefix table every label needs.
function loaded(message) {
  const result = message.result || {};
  if (message.error !== undefined) {
    summary.textContent = "Could not load this page's data: " + message.error;
    return;
  }
  if (result.version !== VERSION) {
    summary.textContent =
      "Unsupported data version " + result.version + "; this page understands " + VERSION + ".";
    return;
  }
  installEntities(result.entityKinds);
  dispatch({ type: "loaded" });
  const { blocks, insts, events } = result.summary;
  summary.textContent = blocks + " blocks, " + insts + " insts, " + events + " events";
}

let searchTimer = null;

function dispatch(action) {
  // The only action the glue delays. A later keystroke replaces the pending
  // one outright, so a burst of typing costs one query.
  if (action.type === "search") {
    clearTimeout(searchTimer);
    searchTimer = setTimeout(() => run(action), SEARCH_DEBOUNCE_MS);
    return;
  }
  run(action);
}

function run(action) {
  const next = handleAction(state, action);
  state = next.state;
  for (const query of next.queries) {
    sent.set(query.id, query);
    post(query);
  }
  render(state);
}

post({ id: LOAD_ID, method: "load", args: [json] });
installView(document.body, dispatch);
render(state);
