// Layer 5: the view.
//
// `render(state)` mutates the DOM to match the state. One-way: the view never
// reads state back out of the DOM and never mutates the state. Listeners are
// installed once, by delegation on the container, and only dispatch actions.
//
// Nothing here decides anything. If a conditional wants to live in this file,
// it belongs in `actions.js`.

import { entityClass, entityLabel } from "./entities.js";

// Wire up the listeners. `dispatch` takes an action.
export function installView(root, dispatch) {
  root.querySelector("#tabs").addEventListener("click", (e) => {
    const tab = e.target.closest("[data-tab]");
    if (tab) dispatch({ type: "selectTab", tab: tab.dataset.tab });
  });

  root.querySelector("#breadcrumbs").addEventListener("click", (e) => {
    const crumb = e.target.closest("[data-index]");
    if (crumb) dispatch({ type: "clickBreadcrumb", index: Number(crumb.dataset.index) });
  });
}

// Draw `state`.
export function render(state) {
  renderTabs(state);
  renderBreadcrumbs(state);
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
