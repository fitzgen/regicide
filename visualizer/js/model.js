// Layer 1: the data model kernel.
//
// Pure. Knows nothing about the DOM, the display, or messages: it takes the
// parsed JSON blob and answers questions about it. This is the layer the node
// tests exercise hardest, because it needs no environment at all.

import { entityClass, entityLabel, installEntities } from "./entities.js";

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
  let outline = null;
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

    // The function pane, rendered. Built once and kept: it is the largest
    // thing the model computes and the pane asks for it exactly once.
    functionOutline: () => (outline ||= buildOutline(func)),

    // The histograms tab. Commit 12.
    histograms: () => json.histograms || [],
  };
}

// ---------------------------------------------------------------------------
// The function outline.
//
// A flat list of lines plus the span bars beside them. Flat, with nesting
// expressed as a `depth`, because every consumer -- the bar geometry, the
// scroll targets, the click handling -- indexes by row, and a tree would have
// to be flattened again by each of them.

// A plain-text part: no entity, not clickable.
const text = (t) => ({ text: t });

// An entity part: the label and the class come from `entities.js`, so the page
// spells an entity the same way everywhere and nothing here builds a label out
// of a prefix and an index.
function entity(kind, index) {
  const ref = { kind, index };
  return { text: entityLabel(ref), entity: ref, cls: entityClass(ref) };
}

// An allocation is one of four shapes, each a bare index under a key that says
// what it indexes.
const ALLOCATION_KINDS = {
  reg: "Reg",
  regGroup: "RegGroup",
  slot: "SpillSlot",
  slotGroup: "SpillSlotGroup",
};

// The entity an allocation names, or `null` if there is none.
function allocationRef(allocation) {
  if (!allocation) return null;
  for (const key of Object.keys(ALLOCATION_KINDS)) {
    if (allocation[key] !== undefined) return { kind: ALLOCATION_KINDS[key], index: allocation[key] };
  }
  return null;
}

// A program point as a single ordinal, so that two can be compared. Early
// precedes late within an instruction.
const at = (point) => point.inst * 2 + (point.pos === "late" ? 1 : 0);

// How a block is prefixed. The kinds are decided in Rust (`BlockKind`) so that
// no threshold is recomputed here.
function blockPrefix(kind) {
  if (kind === "normal") return "";
  if (typeof kind === "string") return kind + " ";
  if (kind && kind.freq !== undefined) return "freq(" + Math.round(kind.freq * 100) / 100 + ") ";
  return "";
}

// `v3[r1]`, or a bare `v2` where the value has no allocation. The brackets are
// plain text and the two entities are separately clickable.
function valueParts(val, allocation) {
  const parts = [entity("Val", val)];
  const ref = allocationRef(allocation);
  if (ref) parts.push(text("["), entity(ref.kind, ref.index), text("]"));
  return parts;
}

// `move r2 to stack0`, `remat v0[r3]`. A critical edge's edit is drawn as the
// edit it carries; the edge itself is already a line.
function editParts(edit) {
  if (edit.criticalEdge) return editParts(edit.criticalEdge.edit);
  if (edit.remat) return [text("remat "), ...valueParts(edit.remat.val, { reg: edit.remat.dest })];
  const move = edit.move;
  if (move && move.regReg) return moveParts("Reg", move.regReg.from, "Reg", move.regReg.to);
  if (move && move.spill) return moveParts("Reg", move.spill.from, "SpillSlot", move.spill.to);
  if (move && move.reload) return moveParts("SpillSlot", move.reload.from, "Reg", move.reload.to);
  // Unreachable unless the Rust side grows a variant; say so rather than
  // dropping the line, which would silently lose an edit.
  return [text("unknown edit")];
}

const moveParts = (fromKind, from, toKind, to) => [
  text("move "),
  entity(fromKind, from),
  text(" to "),
  entity(toKind, to),
];

function buildOutline(func) {
  const blocks = func.blocks || [];
  const insts = func.insts || [];
  const regions = func.regions || [];
  const spans = func.spans || [];
  const uses = func.uses || [];
  const slots = func.spillSlots || [];

  // Spans grouped by value, so that "where is v3 at this point?" does not scan
  // every span in the function.
  const spansByVal = new Map();
  spans.forEach((span, i) => {
    const list = spansByVal.get(span.val);
    if (list === undefined) spansByVal.set(span.val, [i]);
    else list.push(i);
  });

  // An operand's own use says which span it belongs to, which is exact where
  // searching by point is not: two spans of one value abut at the point a
  // reload splits them, and both contain it.
  const useByOperand = new Map();
  for (const use of uses) useByOperand.set(use.point.inst + ":" + use.operand, use);

  // Where `val` lives at `point`, or `null` if nothing covers it. Used for the
  // places that have no operand of their own: block parameters and edge
  // arguments.
  function allocationAt(val, point) {
    if (point === null) return null;
    const p = at(point);
    let covering = null;
    for (const i of spansByVal.get(val) || []) {
      const span = spans[i];
      if (at(span.start) > p || p > at(span.end)) continue;
      // A span that merely touches `point` with an endpoint is the weaker
      // answer: the value arrives or leaves there.
      if (at(span.start) < p && p < at(span.end)) return span.allocation;
      if (covering === null) covering = span.allocation;
    }
    return covering;
  }

  const lines = [];
  const push = (depth, kind, parts) => lines.push({ depth, kind, parts, row: lines.length });
  const blank = () => push(0, "blank", []);

  // Which rows an instruction occupies, for the span bars.
  const instRows = new Map();

  push(0, "function-open", [text("function {")]);

  for (const [i, slot] of slots.entries()) {
    const bytes = slot.size + (slot.size === 1 ? " byte" : " bytes");
    push(1, "slot", [
      entity("SpillSlot", i),
      text(": " + bytes + (slot.emergency ? " (emergency)" : "")),
    ]);
  }

  // A region is named by a block, so the array is sparse; the roots are the
  // regions with no parent.
  let firstAtTop = slots.length === 0;
  regions.forEach((region, i) => {
    if (region && region.parent === null) {
      if (!firstAtTop) blank();
      firstAtTop = false;
      emitRegion(i);
    }
  });

  push(0, "brace-close", [text("}")]);

  function emitRegion(index) {
    const region = regions[index];
    const depth = 1 + region.depth;
    push(depth, "region-open", [entity("Region", index), text(" {")]);
    let first = true;
    for (const block of region.blocks) {
      if (!first) blank();
      first = false;
      emitBlock(block, depth + 1);
    }
    for (const child of region.children) {
      if (!first) blank();
      first = false;
      emitRegion(child);
    }
    push(depth, "brace-close", [text("}")]);
  }

  function emitBlock(index, depth) {
    const block = blocks[index];
    const first = block.insts[0];
    const last = block.insts[block.insts.length - 1];
    // A block with no instructions has no points of its own, and nothing in it
    // can be allocated anywhere.
    const start = first === undefined ? null : { inst: first, pos: "early" };
    const end = last === undefined ? null : { inst: last, pos: "late" };

    const parts = [];
    const prefix = blockPrefix(block.kind);
    if (prefix) parts.push(text(prefix));
    parts.push(entity("Block", index));
    parts.push(...callList(block.params, start));
    parts.push(text(":"));
    push(depth, "block", parts);

    for (const inst of block.insts) emitInst(inst, depth + 1);

    // A block with no successors falls off the end of the function.
    if (block.successors.length === 0) {
      push(depth + 2, "edge", [text("--> returns")]);
      return;
    }
    block.successors.forEach((succ, i) => {
      push(depth + 2, "edge", [
        text("--> "),
        entity("Block", succ),
        ...callList((block.callArgs[i] || []), end),
      ]);
      // The one place indentation is not structural depth: an edge's edits
      // belong to the edge, which is a line and not a scope.
      for (const edgeEdit of block.edgeEdits) {
        if (edgeEdit.succ === i) push(depth + 3, "edge-edit", editParts(edgeEdit.edit));
      }
    });
  }

  // `(v0[r0], v1[r1])`, or nothing at all when the list is empty -- an empty
  // pair of parentheses is noise on every block that takes no parameters.
  function callList(vals, point) {
    if (vals.length === 0) return [];
    const parts = [text("(")];
    vals.forEach((val, i) => {
      if (i) parts.push(text(", "));
      parts.push(...valueParts(val, allocationAt(val, point)));
    });
    parts.push(text(")"));
    return parts;
  }

  function emitInst(index, depth) {
    const inst = insts[index];
    const label = entityLabel({ kind: "Inst", index });

    for (const edit of inst.edits) {
      if (edit.at.pos === "early") push(depth, "edit", editParts(edit.edit));
    }

    const early = operandParts(index, inst, "early");
    const late = operandParts(index, inst, "late");
    const from = lines.length;
    push(depth, "inst", [entity("Inst", index), text(" early:"), ...early]);
    // Right-aligned under `early:`, which is what makes a column of operands
    // readable. Both halves are always drawn, even an empty one.
    push(depth, "inst", [text(" ".repeat(label.length + 2) + "late:"), ...late]);
    instRows.set(index, { first: from, last: lines.length - 1 });

    for (const edit of inst.edits) {
      if (edit.at.pos === "late") push(depth, "edit", editParts(edit.edit));
    }
  }

  function operandParts(index, inst, pos) {
    const parts = [];
    inst.operands.forEach((operand, i) => {
      if (operand.pos !== pos) return;
      const use = useByOperand.get(index + ":" + i);
      const allocation = use === undefined ? null : spans[use.span].allocation;
      parts.push(text(parts.length === 0 ? " " : ", "));
      parts.push(text(operand.defUse + " "), ...valueParts(operand.val, allocation));
    });
    return parts;
  }

  return { lines, bars: buildBars(spans, instRows) };
}

// One bar per span, spanning the rows its instructions occupy.
function buildBars(spans, instRows) {
  const bars = [];
  spans.forEach((span, index) => {
    const start = instRows.get(span.start.inst);
    const end = instRows.get(span.end.inst);
    // A span over an instruction no block claims is not drawable; it would
    // have no rows to sit beside.
    if (start === undefined || end === undefined) return;
    const ref = allocationRef(span.allocation);
    bars.push({
      span: { kind: "LiveSpan", index },
      val: { kind: "Val", index: span.val },
      allocation: ref,
      bundle: span.bundle === null ? null : { kind: "LiveBundle", index: span.bundle },
      label:
        entityLabel({ kind: "LiveSpan", index }) +
        "(" +
        entityLabel({ kind: "Val", index: span.val }) +
        (ref ? "[" + entityLabel(ref) + "]" : "") +
        ")",
      startRow: start.first,
      endRow: end.last,
      column: 0,
    });
  });

  // Interval-graph coloring: in start order, each bar takes the leftmost
  // column whose last bar has already ended. Greedy is optimal here, and it
  // keeps the bar field as narrow as the overlaps allow.
  bars.sort((a, b) => a.startRow - b.startRow || a.endRow - b.endRow);
  const columnEnds = [];
  for (const bar of bars) {
    let column = columnEnds.findIndex((end) => end < bar.startRow);
    if (column === -1) column = columnEnds.length;
    columnEnds[column] = bar.endRow;
    bar.column = column;
  }
  return bars;
}
