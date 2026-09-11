// Layer 5: the view.
//
// `render(state)` mutates the DOM to match the state. One-way: the view never
// reads state back out of the DOM and never mutates the state. Listeners are
// installed once, by delegation on the container, and only dispatch actions.
//
// Nothing here decides anything. If a conditional wants to live in this file,
// it belongs in `actions.js`.

import { bundleColor, entityClass, entityKey, entityLabel, sameEntity } from "./entities.js";

// How many spaces one level of nesting is worth in the function pane.
const INDENT = 4;

// The action dispatcher, kept so that the scroll handshake can be closed from
// here: the view scrolls, then says it has.
//
// Qualified, like `installView`: the stitched page concatenates this file with
// `main.js`, whose own `dispatch` is a top-level function, and two top-level
// bindings of one name is a syntax error there and nowhere else.
let viewDispatch = () => {};

// The outline the function pane's DOM was built from. Building it is the
// expensive step -- thousands of lines -- so it happens once and every later
// render only touches the classes that change.
let built = null;

// `entityKey` -> the ref it came from, so that a click hands `actions.js` a
// real ref and nothing parses a string back into one.
let refs = new Map();

// `entityKey` -> its elements in document order, for scrolling and selection.
let elements = new Map();

// The bars, with the bundle each belongs to, for the hover highlight.
let bars = [];

// What the classes on screen currently reflect, so that an unrelated re-render
// does no work.
let shownSelection = null;
let shownHover = null;

// Wire up the listeners. `dispatcher` takes an action.
export function installView(root, dispatcher) {
  viewDispatch = dispatcher;

  root.querySelector("#tabs").addEventListener("click", (e) => {
    const tab = e.target.closest("[data-tab]");
    if (tab) viewDispatch({ type: "selectTab", tab: tab.dataset.tab });
  });

  root.querySelector("#breadcrumbs").addEventListener("click", (e) => {
    const crumb = e.target.closest("[data-index]");
    if (crumb) viewDispatch({ type: "clickBreadcrumb", index: Number(crumb.dataset.index) });
  });

  // One handler for the whole pane, on the pane itself: the lines and bars are
  // rebuilt wholesale, and per-element listeners would have to be rebuilt with
  // them.
  const pane = root.querySelector("#function-pane");
  pane.addEventListener("click", (e) => {
    const el = e.target.closest("[data-entity]");
    const ref = el && refs.get(el.dataset.entity);
    if (ref) viewDispatch({ type: "clickEntity", ref });
  });
  pane.addEventListener("mouseover", (e) => {
    const bar = e.target.closest(".bar");
    if (bar) viewDispatch({ type: "hoverSpan", ref: refs.get(bar.dataset.entity) });
  });
  pane.addEventListener("mouseout", (e) => {
    if (e.target.closest(".bar")) viewDispatch({ type: "unhoverSpan" });
  });
}

// Draw `state`.
export function render(state) {
  renderTabs(state);
  renderBreadcrumbs(state);
  renderFunction(state);
}

function renderTabs(state) {
  for (const button of document.querySelectorAll("#tabs [data-tab]")) {
    const active = button.dataset.tab === state.tab;
    button.classList.toggle("active", active);
    button.setAttribute("aria-selected", String(active));
  }
  for (const panel of document.querySelectorAll("[data-panel]")) {
    panel.hidden = panel.dataset.panel !== state.tab;
  }
}

// Rebuilt whole on every render. The bar holds a handful of elements, so a
// diffing layer would be all cost and no benefit.
function renderBreadcrumbs(state) {
  const bar = document.getElementById("breadcrumbs");
  bar.textContent = "";
  state.breadcrumbs.forEach((ref, i) => {
    // A real button, so that the trail is Tab-navigable.
    const crumb = document.createElement("button");
    crumb.type = "button";
    crumb.className = "crumb " + entityClass(ref);
    if (i === state.activeBreadcrumb) crumb.classList.add("active");
    crumb.dataset.index = String(i);
    crumb.textContent = entityLabel(ref);
    bar.append(crumb);
  });
}

function renderFunction(state) {
  if (state.outline !== built) buildFunction(state.outline);
  applyFunctionState(state);
  scrollToEntity(state);
}

// Build the pane's DOM from an outline.
//
// Deliberately not virtualized: rendering every line keeps `scrollIntoView`,
// the browser's own find, and the bar geometry (a row number times a line
// height, over the whole document) trivially correct, and all three get harder
// the moment rows are recycled.
function buildFunction(outline) {
  const pane = document.getElementById("function-pane");
  pane.textContent = "";
  built = outline;
  refs = new Map();
  elements = new Map();
  bars = [];
  shownSelection = null;
  shownHover = null;
  if (!outline) return;

  // The two layers are siblings inside a positioned wrapper, so that a long
  // bar label cannot shift the text, and the wrapper's height comes from the
  // text alone.
  const body = document.createElement("div");
  body.className = "function-body";
  const barLayer = document.createElement("div");
  barLayer.className = "bar-layer";
  const textLayer = document.createElement("div");
  textLayer.className = "text-layer";

  for (const line of outline.lines) {
    const el = document.createElement("div");
    el.className = "line line-" + line.kind;
    // Real spaces rather than padding, so that a selection copied out of the
    // pane keeps its shape.
    el.append(" ".repeat(line.depth * INDENT));
    for (const part of line.parts) {
      if (!part.entity) {
        el.append(part.text);
        continue;
      }
      const span = document.createElement("span");
      span.className = "ent " + part.cls;
      span.textContent = part.text;
      remember(span, part.entity);
      el.append(span);
    }
    textLayer.append(el);
  }

  // The pane is monospace with a fixed line height, so a bar's geometry is
  // arithmetic on its rows and nothing has to be measured.
  const style = getComputedStyle(pane);
  const lineHeight = parseFloat(style.getPropertyValue("--line-height"));
  const barWidth = parseFloat(style.getPropertyValue("--bar-width"));
  let columns = 0;
  for (const bar of outline.bars) {
    const el = document.createElement("div");
    el.className = "bar";
    el.style.top = bar.startRow * lineHeight + "px";
    el.style.height = (bar.endRow - bar.startRow + 1) * lineHeight + "px";
    el.style.left = bar.column * barWidth + "px";
    // A span that never reached a bundle has no color of its own.
    el.style.background = bar.bundle === null ? "var(--fg-dim)" : bundleColor(bar.bundle.index);
    const label = document.createElement("span");
    label.className = "bar-label";
    label.textContent = bar.label;
    el.append(label);
    remember(el, bar.span);
    barLayer.append(el);
    bars.push({ el, bundle: bar.bundle });
    columns = Math.max(columns, bar.column + 1);
  }

  barLayer.style.width = columns * barWidth + "px";
  textLayer.style.marginLeft = columns * barWidth + "px";
  body.append(barLayer, textLayer);
  pane.append(body);
}

// Make `el` the clickable, scrollable stand-in for `ref`.
function remember(el, ref) {
  const key = entityKey(ref);
  el.dataset.entity = key;
  refs.set(key, ref);
  const found = elements.get(key);
  if (found === undefined) elements.set(key, [el]);
  else found.push(el);
}

// Everything that changes without the DOM being rebuilt.
function applyFunctionState(state) {
  const selection = state.selected === null ? null : entityKey(state.selected);
  if (selection !== shownSelection) {
    for (const el of elements.get(shownSelection) || []) el.classList.remove("selected");
    for (const el of elements.get(selection) || []) el.classList.add("selected");
    shownSelection = selection;
  }

  const hover = state.hoveredBundle;
  if (!sameEntity(hover, shownHover) && !(hover === null && shownHover === null)) {
    for (const bar of bars) {
      bar.el.classList.toggle("dimmed", hover !== null && !sameEntity(bar.bundle, hover));
    }
    shownHover = hover;
  }
}

// The other half of commit 08's one-shot: scroll, then report that the request
// has been served. Cleared even when nothing matches -- the entity may be real
// but drawn nowhere, and a request that never clears blocks the next one.
function scrollToEntity(state) {
  if (state.scrollToEntity === null) return;
  const found = elements.get(entityKey(state.scrollToEntity));
  if (found) found[0].scrollIntoView({ block: "center" });
  // Out of band: dispatching from inside a render would re-enter it.
  queueMicrotask(() => viewDispatch({ type: "scrolled", what: "entity" }));
}
