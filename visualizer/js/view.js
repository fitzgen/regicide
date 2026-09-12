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

// The event log's scroll position and the results it was drawn against.
//
// The one thing the view keeps that the state does not. A virtualized list
// re-renders on every scroll frame, and routing that through `handleAction`
// would be an action per frame for something derived purely from the scroll
// offset: it is not application state, nothing else reads it, and it does not
// survive a rebuild. Rows are a different matter and do live in the state --
// they come from the worker -- and so does the set of indices already asked
// for, which is what stops a render triggered by the answer from asking again.
// That set was once kept here too, but only the reducer sees a query fail, and
// a failed query has to be un-asked or its rows stay blank for good.
let eventScroll = 0;
let shownResults = null;

// How far the details pane can be dragged. Narrower than this and a field's
// label and value no longer fit on one line; wider and the function pane it
// exists to annotate is gone.
const MIN_DETAILS_WIDTH = 180;
const MAX_DETAILS_WIDTH = 900;

// The histograms the pane and the table of contents were built from. Both
// are static once they arrive, so each is built once and then left alone.
let builtHistograms = null;
let builtGroups = null;

// A histogram id -> its heading, for the table of contents' scroll.
let histogramHeadings = new Map();
// The state the last render drew, so that a scroll can redraw the window
// without one being passed in.
let lastState = null;

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
  // Any entity, not just a bar: hovering one previews it in the details pane,
  // and a bar still drives the bundle-wide dim as well.
  pane.addEventListener("mouseover", (e) => {
    const el = e.target.closest("[data-entity]");
    const ref = el && refs.get(el.dataset.entity);
    if (ref) viewDispatch({ type: "hoverEntity", ref });
  });
  pane.addEventListener("mouseout", (e) => {
    if (e.target.closest("[data-entity]") === null) return;
    // Moving from a bar to its own label, or straight from one entity to the
    // next, is not leaving: the `mouseover` that follows would only have to
    // undo this, and the pane would flicker in between.
    const into = e.relatedTarget;
    if (into && into.closest && into.closest("[data-entity]")) return;
    viewDispatch({ type: "unhoverEntity" });
  });

  root.querySelector("#event-query").addEventListener("input", (e) => {
    viewDispatch({ type: "search", query: e.target.value });
  });

  // Clicking a reference in the log leaves the log: the function tab is where
  // an entity can actually be looked at, and `actions.js` is what decides
  // that.
  const list = root.querySelector("#event-list");
  list.addEventListener("click", (e) => {
    const el = e.target.closest("[data-entity]");
    const ref = el && refs.get(el.dataset.entity);
    if (ref) viewDispatch({ type: "clickEntityFromEvent", entity: ref });
  });

  root.querySelector("#histogram-toc").addEventListener("click", (e) => {
    const entry = e.target.closest("[data-histogram-id]");
    if (entry) viewDispatch({ type: "scrollToHistogram", id: entry.dataset.histogramId });
  });
  // Straight to the renderer, per the note on `eventScroll`.
  list.addEventListener("scroll", () => {
    eventScroll = list.scrollTop;
    if (lastState !== null) renderEventRows(lastState);
  });

  installResizer(root);
}

// Dragging the handle sets the details pane's width, in the view and not in
// the state, for the reason given on `eventScroll`: a drag is a stream of
// events at frame rate and nothing else reads the width. It survives a render
// because `#details-pane` itself is never rebuilt, only its children.
function installResizer(root) {
  const resizer = root.querySelector("#details-resizer");
  const details = root.querySelector("#details-pane");

  resizer.addEventListener("pointerdown", (e) => {
    // The pane is on the right, so dragging left widens it.
    const startX = e.clientX;
    const startWidth = details.getBoundingClientRect().width;
    const move = (e) => {
      const width = startWidth - (e.clientX - startX);
      details.style.width = Math.min(MAX_DETAILS_WIDTH, Math.max(MIN_DETAILS_WIDTH, width)) + "px";
    };
    const up = () => {
      resizer.removeEventListener("pointermove", move);
      resizer.removeEventListener("pointerup", up);
      root.classList.remove("resizing");
    };

    root.classList.add("resizing");
    resizer.addEventListener("pointermove", move);
    resizer.addEventListener("pointerup", up);
    // Capture last, and on the handle the listeners are on: a pointer that
    // outruns the 5px strip keeps driving the drag rather than dropping it on
    // the first fast flick.
    resizer.setPointerCapture(e.pointerId);
    e.preventDefault();
  });
}

// Draw `state`.
export function render(state) {
  lastState = state;
  renderTabs(state);
  renderBreadcrumbs(state);
  renderFunction(state);
  renderDetails(state);
  renderEvents(state);
  renderHistograms(state);
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

  // Counted up front, because the columns are laid out right to left: the
  // first column sits against the text it describes, where the eye already
  // is, and later columns stack away from it.
  const columns = outline.bars.reduce((n, bar) => Math.max(n, bar.column + 1), 0);

  for (const bar of outline.bars) {
    const el = document.createElement("div");
    el.className = "bar";
    el.style.top = bar.startRow * lineHeight + "px";
    el.style.height = (bar.endRow - bar.startRow + 1) * lineHeight + "px";
    el.style.left = (columns - 1 - bar.column) * barWidth + "px";
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

// The other half of the one-shot: scroll, then report that the request has
// been served. Cleared even when nothing matches -- the entity may be real but
// drawn nowhere, and a request that never clears blocks the next one.
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
  // The hover wins while there is one, and dropping it restores the selection.
  const shown = state.hovered !== null ? state.hovered : state.selected;
  if (shown === null) return;

  // Always read the cache at the *shown* key, so that a result arriving for an
  // entity the pointer has already left cannot appear.
  const key = entityKey(shown);
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

// ---------------------------------------------------------------------------
// The event log tab.

// How many rows beyond the visible window to draw, so that a fast scroll does
// not show a blank strip before the next frame catches up.
const EVENT_OVERSCAN = 10;

// The search field, the count, and the list.
function renderEvents(state) {
  const input = document.getElementById("event-query");
  // Never while the field has focus: the state lags the field by the search
  // debounce, and assigning `value` mid-word moves the caret to the end.
  if (document.activeElement !== input && input.value !== state.search.query) {
    input.value = state.search.query;
  }

  const results = state.search.results;
  const count = document.getElementById("event-count");
  count.textContent =
    results === null ? "" : results.length === 1 ? "1 event" : results.length + " events";

  // A new set of results is a new list, and the browser keeps `scrollTop`
  // across the rebuild: the old offset would land the user somewhere
  // arbitrary in it.
  if (results !== shownResults) {
    shownResults = results;
    eventScroll = 0;
    document.getElementById("event-list").scrollTop = 0;
  }
  renderEventRows(state);
  scrollToEvent(state);
}

// The same one-shot as the other two panes', with one difference: it is not
// cleared when the event is nowhere to be found.
//
// The other two clear regardless, because an entity absent from the DOM is an
// entity that will never be there. An event absent from the results may be one
// the request itself is fetching -- `showEvent` clears a filter that hides the
// event -- so clearing here would drop the scroll a frame before the results
// it needs arrive. An unsettled search is left pending instead, and the next
// render serves it.
function scrollToEvent(state) {
  if (state.scrollToEvent === null) return;
  const results = state.search.results;
  if (results === null || state.search.pending) return;

  const at = results.indexOf(state.scrollToEvent);
  if (at >= 0) {
    // No element to `scrollIntoView`: the list is virtualized, so the offset
    // is arithmetic on `--event-row`, as in `renderEventRows`. Half a row of
    // slack centres the row itself rather than its top edge.
    const list = document.getElementById("event-list");
    const rowHeight = parseFloat(getComputedStyle(list).getPropertyValue("--event-row"));
    list.scrollTop = Math.max(0, (at + 0.5) * rowHeight - list.clientHeight / 2);
    // Read back, because the browser clamps the bottom end, and then redraw:
    // the window this lands on is not the one just drawn.
    eventScroll = list.scrollTop;
    renderEventRows(state);
  }
  queueMicrotask(() => viewDispatch({ type: "scrolled", what: "event" }));
}

// The rows, drawn on every scroll as well as every render.
//
// Virtualized: a spacer gives the scrollbar the height the whole log would
// have, and only the rows in view are in the DOM. A log of two hundred
// thousand events is two hundred thousand elements otherwise, which no
// browser will draw. The spacer is kept between redraws rather than rebuilt,
// because emptying the container would collapse its height and the browser
// would clamp `scrollTop` to the top.
function renderEventRows(state) {
  const list = document.getElementById("event-list");
  const results = state.search.results;
  if (results === null || results.length === 0) {
    list.textContent = "";
    if (results === null) return;
    const empty = document.createElement("p");
    empty.className = "event-empty";
    // The distinction matters: a log with no events at all is a different
    // thing from a query that matched none of them.
    empty.textContent = state.search.query === "" ? "No events." : "No matches.";
    list.append(empty);
    return;
  }

  // Arithmetic on a fixed row height, like the function pane's bars: a row is
  // one line of preformatted text, so nothing has to be measured.
  const rowHeight = parseFloat(getComputedStyle(list).getPropertyValue("--event-row"));
  const first = Math.max(0, Math.floor(eventScroll / rowHeight) - EVENT_OVERSCAN);
  const visible = Math.ceil((eventScroll + list.clientHeight) / rowHeight) + EVENT_OVERSCAN;
  const last = Math.min(results.length, visible);

  let spacer = list.querySelector(".event-spacer");
  let rows = spacer && spacer.firstChild;
  if (spacer === null) {
    list.textContent = "";
    spacer = document.createElement("div");
    spacer.className = "event-spacer";
    rows = document.createElement("ol");
    rows.className = "event-rows";
    spacer.append(rows);
    list.append(spacer);
  }
  spacer.style.height = results.length * rowHeight + "px";
  rows.style.transform = "translateY(" + first * rowHeight + "px)";
  rows.textContent = "";

  const missing = [];
  for (let i = first; i < last; i++) {
    const index = results[i];
    const row = state.eventRows[index];
    const item = document.createElement("li");
    item.className = "event-row";
    const label = document.createElement("span");
    label.className = entityClass({ kind: "EventIndex", index });
    // Not clickable, unlike the references inside the row: this is the line
    // the user is already looking at.
    label.textContent = entityLabel({ kind: "EventIndex", index });
    item.append(label, " ");
    if (row === undefined) {
      // The rows for this window are on their way. A placeholder rather than
      // a blank line, so the list does not look like it ends here.
      missing.push(index);
      item.classList.add("event-row-pending");
      item.append("…");
    } else {
      // The same parts the details pane renders, through the same function,
      // so an entity is spelled and coloured identically in both.
      appendParts(item, row.summary, { swatch: true });
    }
    rows.append(item);
  }

  // Asked for out of band, because dispatching from inside a render would
  // re-enter it, and only for what is not already in flight, so that the
  // render which draws the answer cannot ask for it again.
  const wanted = missing.filter((index) => state.askedRows[index] === undefined);
  if (wanted.length > 0) {
    queueMicrotask(() => viewDispatch({ type: "needEventRows", indices: wanted }));
  }
}

// ---------------------------------------------------------------------------
// The histograms tab.

// Built once each, then only the scroll handshake runs. The histograms are
// pre-computed and never change, which is what makes a cache here correct
// rather than merely fast.
function renderHistograms(state) {
  if (state.histogramGroups !== builtGroups) buildHistogramToc(state.histogramGroups);
  if (state.histograms !== builtHistograms) buildHistogramPane(state.histograms);
  scrollToHistogram(state);
}

// The table of contents: a heading per group, a button per histogram.
function buildHistogramToc(groups) {
  const toc = document.getElementById("histogram-toc");
  toc.textContent = "";
  builtGroups = groups;
  if (!groups) return;

  for (const { group, items } of groups) {
    const heading = document.createElement("h2");
    heading.className = "toc-group";
    heading.textContent = group;
    toc.append(heading);

    const list = document.createElement("ul");
    list.className = "toc-items";
    for (const item of items) {
      const entry = document.createElement("li");
      const button = document.createElement("button");
      button.type = "button";
      button.className = "toc-item";
      // Greyed rather than hidden or disabled: a function with no spills
      // should read as "nothing to see here", and the entry is still worth
      // scrolling to in order to see that it says so.
      if (item.count === 0) button.classList.add("toc-empty");
      button.dataset.histogramId = item.id;
      const title = document.createElement("span");
      title.textContent = item.title;
      const count = document.createElement("span");
      count.className = "toc-count";
      count.textContent = String(item.count);
      button.append(title, count);
      entry.append(button);
      list.append(entry);
    }
    toc.append(list);
  }
}

// The pane: a section per histogram.
function buildHistogramPane(histograms) {
  const pane = document.getElementById("histogram-pane");
  pane.textContent = "";
  builtHistograms = histograms;
  histogramHeadings = new Map();
  if (!histograms) return;

  for (const histogram of histograms) {
    const section = document.createElement("section");
    section.className = "histogram";

    const heading = document.createElement("h2");
    heading.className = "histogram-title";
    // The id goes on the heading rather than the section, so that scrolling
    // to it puts the title at the top of the pane rather than above it.
    heading.id = "histogram-" + histogram.id;
    heading.textContent = histogram.title;
    histogramHeadings.set(histogram.id, heading);
    section.append(heading);

    section.append(histogramStats(histogram));
    if (histogram.count > 0) section.append(histogramBars(histogram));
    pane.append(section);
  }
}

// The stats line.
function histogramStats(histogram) {
  const stats = document.createElement("p");
  stats.className = "histogram-stats";
  if (histogram.count === 0) {
    stats.textContent = "no samples";
    return stats;
  }
  // A mean over no samples is not zero, and printing `0.00` there would claim
  // a measurement nobody took. It arrives finite, so nothing here has to guard
  // against `NaN`, but "no samples" is still the honest reading.
  const parts = [
    ["count", histogram.count],
    ["min", histogram.min],
    ["max", histogram.max],
    ["mean", histogram.mean.toFixed(2)],
    ["p50", histogram.p50],
    ["p90", histogram.p90],
    ["p99", histogram.p99],
  ];
  for (const [label, value] of parts) {
    const stat = document.createElement("span");
    stat.className = "histogram-stat";
    const name = document.createElement("span");
    name.className = "histogram-stat-name";
    name.textContent = label;
    stat.append(name, " " + value);
    stats.append(stat);
  }
  return stats;
}

// The bars. Flexbox rows over the bucket list: a label, a bar scaled to the
// fullest bucket, and the count. No canvas and no library -- the page is one
// self-contained file, and a bar chart is a div whose width is a percentage.
function histogramBars(histogram) {
  const buckets = histogram.buckets || [];
  const widest = Math.max(1, ...buckets.map((bucket) => bucket.count));

  const table = document.createElement("div");
  table.className = "histogram-bars";
  for (const bucket of buckets) {
    const row = document.createElement("div");
    row.className = "histogram-bucket";

    const label = document.createElement("span");
    label.className = "bucket-label";
    // An en dash range only when the bucket spans more than one value: `3-3`
    // is noise, and most of the interesting buckets are one value wide.
    label.textContent = bucket.lo === bucket.hi ? String(bucket.lo) : bucket.lo + "–" + bucket.hi;

    const track = document.createElement("span");
    track.className = "bucket-track";
    const bar = document.createElement("span");
    bar.className = "bucket-bar";
    // Empty buckets are drawn at zero width rather than skipped: a gap in the
    // middle of a distribution is a fact about it, and dropping the row would
    // make the axis lie.
    bar.style.width = (bucket.count / widest) * 100 + "%";
    track.append(bar);

    const count = document.createElement("span");
    count.className = "bucket-count";
    count.textContent = String(bucket.count);

    row.append(label, track, count);
    table.append(row);
  }
  return table;
}

// The same one-shot, for the other pane. Cleared even when no histogram
// matches -- an id that is in the state but not in the DOM would otherwise
// have every later render retrying it forever.
function scrollToHistogram(state) {
  if (state.scrollToHistogram === null) return;
  const heading = histogramHeadings.get(state.scrollToHistogram);
  if (heading) heading.scrollIntoView({ block: "start" });
  queueMicrotask(() => viewDispatch({ type: "scrolled", what: "histogram" }));
}
