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

// `entityKey` of a span -> the bundle it was placed in, taken from the bars.
// The details pane colours a span with its bundle's color, and the outline is
// the only thing that knows which that is.
let spanBundles = new Map();

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

  // One handler per pane, on the pane itself: the lines, bars and fields are
  // rebuilt wholesale, and per-element listeners would have to be rebuilt with
  // them. Both panes share it, so that clicking a reference in the details
  // pane does exactly what clicking one in the function pane does -- including
  // scrolling the function pane to it.
  const clickEntity = (e) => {
    const el = e.target.closest("[data-entity]");
    const ref = el && refs.get(el.dataset.entity);
    if (ref) viewDispatch({ type: "clickEntity", ref });
  };
  const pane = root.querySelector("#function-pane");
  pane.addEventListener("click", clickEntity);
  root.querySelector("#details-pane").addEventListener("click", clickEntity);
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
  renderDetails(state);
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
  spanBundles = new Map();
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
    // No swatches here: the pane's columns only line up because every
    // character in it is one monospace cell wide, and the bars beside it
    // already carry the colour.
    appendParts(el, line.parts, { track: true });
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
    spanBundles.set(entityKey(bar.span), bar.bundle);
    barLayer.append(el);
    bars.push({ el, bundle: bar.bundle });
    columns = Math.max(columns, bar.column + 1);
  }

  barLayer.style.width = columns * barWidth + "px";
  textLayer.style.marginLeft = columns * barWidth + "px";
  body.append(barLayer, textLayer);
  pane.append(body);
}

// Make `el` a clickable stand-in for `ref`.
//
// The ref itself is kept, rather than reparsed out of the key on click: a page
// that can turn a string back into a ref has two spellings of every entity,
// and they will disagree.
function rememberRef(el, ref) {
  const key = entityKey(ref);
  el.dataset.entity = key;
  refs.set(key, ref);
  return key;
}

// Make `el` the clickable, scrollable stand-in for `ref`.
//
// Only for the function pane: `elements` is what selection and scrolling are
// applied to between rebuilds, and the details pane is rebuilt every render,
// so tracking its elements would fill the map with detached ones.
function remember(el, ref) {
  const key = rememberRef(el, ref);
  const found = elements.get(key);
  if (found === undefined) elements.set(key, [el]);
  else found.push(el);
}

// Render a `parts` array -- the model's one renderable shape -- into `el`.
//
// The only place an entity reference becomes DOM, so the function pane and the
// details pane cannot spell the same entity two ways.
function appendParts(el, parts, { swatch = false, track = false } = {}) {
  for (const part of parts) {
    if (!part.entity) {
      el.append(part.text);
      continue;
    }
    const span = document.createElement("span");
    span.className = "ent " + part.cls;
    if (swatch) {
      const chip = swatchFor(part.entity);
      if (chip) span.append(chip);
    }
    span.append(part.text);
    if (track) remember(span, part.entity);
    else rememberRef(span, part.entity);
    el.append(span);
  }
}

// The bundle colour for a bundle or for a span, or nothing for anything else.
// Clicking through from a bar to its bundle should look continuous, which it
// only does if both are drawn in the bundle's own color.
function swatchFor(ref) {
  const bundle =
    ref.kind === "LiveBundle"
      ? ref
      : ref.kind === "LiveSpan"
        ? spanBundles.get(entityKey(ref))
        : null;
  if (!bundle) return null;
  const chip = document.createElement("span");
  chip.className = "swatch";
  chip.style.background = bundleColor(bundle.index);
  return chip;
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

// Rebuilt whole on every render. The pane is a few dozen fields, and the
// selection changing rewrites nearly all of them anyway.
function renderDetails(state) {
  const pane = document.getElementById("details-pane");
  pane.textContent = "";
  if (state.selected === null) return;

  // Always read the cache at the *selected* key, so that a result arriving for
  // an entity the user has already clicked away from cannot appear.
  const key = entityKey(state.selected);
  const details = state.details[key];
  if (!details) {
    // No result and no request means the query failed. An empty pane is honest
    // about knowing nothing; "Loading…" there would look like a hang.
    if (state.pendingDetails === key) {
      const loading = document.createElement("p");
      loading.className = "details-loading";
      loading.textContent = "Loading…";
      pane.append(loading);
    }
    return;
  }

  const head = document.createElement("h2");
  head.className = "details-head " + entityClass(details.ref);
  const chip = swatchFor(details.ref);
  if (chip) head.append(chip);
  // Not clickable: it is already the selection, and clicking it would push a
  // breadcrumb that goes nowhere.
  head.append(entityLabel(details.ref));
  pane.append(head);

  const fields = document.createElement("dl");
  fields.className = "details-fields";
  for (const field of details.fields) {
    const label = document.createElement("dt");
    // The count is the true total, so it reads "(1204)" beside a list of 200.
    label.textContent = field.label + (field.count === undefined ? "" : " (" + field.count + ")");
    const value = document.createElement("dd");
    appendParts(value, field.value, { swatch: true });
    fields.append(label, value);
  }
  pane.append(fields);

  const heading = document.createElement("h3");
  heading.className = "details-heading";
  heading.textContent = "Events (" + details.eventCount + ")";
  pane.append(heading);

  const events = document.createElement("ol");
  events.className = "details-events";
  for (const event of details.events) {
    const item = document.createElement("li");
    const ref = { kind: "EventIndex", index: event.index };
    const link = { text: entityLabel(ref), entity: ref, cls: entityClass(ref) };
    appendParts(item, [link, { text: " " }, ...event.summary], { swatch: true });
    events.append(item);
  }
  if (details.eventCount > details.events.length) {
    const more = document.createElement("li");
    more.className = "details-more";
    more.textContent = "…and " + (details.eventCount - details.events.length) + " more";
    events.append(more);
  }
  pane.append(events);
}
