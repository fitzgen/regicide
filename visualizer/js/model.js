// Layer 1: the data model kernel.
//
// Pure. Knows nothing about the DOM, the display, or messages: it takes the
// parsed JSON blob and answers questions about it. This is the layer the node
// tests exercise hardest, because it needs no environment at all.

import { install } from "./entities.js";

// Read a serialized `SecondaryMap`.
//
// `values` stops at the highest key the allocator ever wrote, so it is short
// whenever the trailing entities were never touched; indexing it directly is a
// bug that only shows up on some inputs. `PrimaryMap`s are bare arrays and need
// no accessor.
const secondary = (map, index) => (index < map.values.length ? map.values[index] : map.default);

// Build the model over a parsed blob.
export function createModel(json) {
  install(json.entityKinds || {});

  const index = json.index || {};
  const byEntity = index.byEntity || {};

  // The events an entity is named by. Kinds with no index of their own (a
  // register unit, say) have no list rather than an empty one.
  const entityEvents = (ref) => {
    const map = byEntity[ref.kind];
    return map === undefined ? [] : secondary(map, ref.index);
  };

  return {
    // Raw lookups.
    event: (i) => (json.events || [])[i],
    entity: (ref) => ({ ref, events: entityEvents(ref) }),

    // The details pane. Commit 10.
    details: (_ref) => ({ fields: [], related: [] }),

    // The event log tab's search. Commit 11.
    searchEvents: (_query) => [],

    // The function pane's renderable tree. Commit 09.
    functionOutline: () => ({ blocks: [] }),

    // The histograms tab. Commit 12.
    histograms: () => json.histograms || [],
  };
}
