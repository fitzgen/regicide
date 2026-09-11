// Layer 1: the data model kernel.
//
// Pure. Knows nothing about the DOM, the display, or messages: it takes the
// parsed JSON blob and answers questions about it. This is the layer the node
// tests exercise hardest, because it needs no environment at all.

import { installEntities } from "./entities.js";

// Read a serialized `SecondaryMap`.
//
// `values` stops at the highest key the allocator ever wrote, so it is short
// whenever the trailing entities were never touched; indexing it directly is a
// bug that only shows up on some inputs. `PrimaryMap`s are bare arrays and need
// no accessor.
const secondary = (map, index) => (index < map.values.length ? map.values[index] : map.default);

// Build the model over a parsed blob.
export function createModel(json) {
  installEntities(json.entityKinds || {});

  const func = json.function || {};
  const index = json.index || {};
  const byEntity = index.byEntity || {};

  // The events an entity is named by. Kinds with no index of their own (a
  // register unit, say) have no list rather than an empty one.
  const entityEvents = (ref) => {
    const map = byEntity[ref.kind];
    return map === undefined ? [] : secondary(map, ref.index);
  };

  return {
    // How big the function is. The load response carries it, so the page can
    // say something true about the blob before any pane exists; commit 09
    // replaces it with the function itself.
    summary: () => ({
      blocks: (func.blocks || []).length,
      insts: (func.insts || []).length,
      events: (json.events || []).length,
    }),

    // Raw lookups.
    event: (i) => (json.events || [])[i],
    entity: (ref) => ({ ref, events: entityEvents(ref) }),

    // The details pane. Commit 10. The result carries its own `ref` back, so
    // that the main thread can cache it without tracking which request it
    // answered.
    details: (ref) => ({ ref, fields: [], events: [] }),

    // The event log tab's search. Commit 11.
    searchEvents: (_query) => [],

    // The function pane's renderable tree. Commit 09.
    functionOutline: () => ({ blocks: [] }),

    // The histograms tab. Commit 12.
    histograms: () => json.histograms || [],
  };
}
