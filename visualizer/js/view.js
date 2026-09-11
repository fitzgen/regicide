// Layer 5: the view.
//
// `render(state)` mutates the DOM to match the state. One-way: the view never
// reads state back out of the DOM and never mutates the state. Listeners are
// installed once, by delegation on the container, and only dispatch actions.
//
// Nothing here decides anything. If a conditional wants to live in this file,
// it belongs in `actions.js`.

// Wire up the listeners. `dispatch` takes an action.
export function installView(root, dispatch) {
  root.addEventListener("click", (e) => {
    const tab = e.target.closest("[data-tab]");
    if (tab) dispatch({ type: "selectTab", tab: tab.dataset.tab });
  });
}

// Draw `state`.
export function render(state) {
  for (const button of document.querySelectorAll("[data-tab]")) {
    button.setAttribute("aria-selected", String(button.dataset.tab === state.tab));
  }
  for (const panel of document.querySelectorAll("[data-panel]")) {
    panel.hidden = panel.dataset.panel !== state.tab;
  }
}
