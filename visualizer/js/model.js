// Layer 1: the data model kernel.
//
// Pure. Knows nothing about the DOM, the display, or messages: it takes the
// parsed JSON blob and answers questions about it. This is the layer the node
// tests exercise hardest, because it needs no environment at all.

import { entityClass, entityLabel, installEntities, parseEntityLabel } from "./entities.js";

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
  // Both are built on first use: the indexes they need are proportional to the
  // whole function, and a page whose user never clicks anything never pays.
  let details = null;
  const index = json.index || {};
  const byEntity = index.byEntity || {};
  const byKind = index.byKind || {};
  const eventSchema = (json.schema || {}).events || {};

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

    // The details pane. The result carries its own `ref` back, so that the
    // main thread can cache it without tracking which request it answered,
    // and `null` says there is no such entity.
    details: (ref) => (details ||= buildDetails(json, entityEvents)).details(ref),

    // The event log tab's search: which events match, in log order. Indices
    // only -- the log is the one list that can be hundreds of thousands long,
    // and `eventRows` is what turns a window of it into something renderable.
    searchEvents: (query) => searchEvents(json, byKind, entityEvents, query),

    // Those events, rendered. Split from the search so that a query matching
    // the whole log answers with an array of numbers rather than an array of
    // summaries: the log is the one list that can be hundreds of thousands
    // long, and only the rows the list actually shows are worth building.
    eventRows: (indices) => {
      const events = json.events || [];
      return (indices || [])
        .filter((i) => i >= 0 && i < events.length)
        .map((i) => eventRow(events, eventSchema, i));
    },

    // The function pane, rendered. Built once and kept: it is the largest
    // thing the model computes and the pane asks for it exactly once.
    functionOutline: () => (outline ||= buildOutline(func)),

    // The histograms tab. The blob's own array, unchanged: commit 05
    // computed every statistic, and recomputing any of them here would be a
    // second answer to a question that already has one.
    histograms: () => json.histograms || [],

    // The same histograms, grouped for the table of contents.
    histogramGroups: () => groupHistograms(json.histograms || []),
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

// ---------------------------------------------------------------------------
// The details pane.
//
// One field list per entity kind, in the order the spec lists them, plus the
// events that name the entity. Every field's value is the same `parts` array
// the function outline uses, so the view renders a clickable entity reference
// in exactly one place.

// How many entries of a list, or events, are rendered. An entity in a large
// function can appear in thousands of events, and the pane is not the event
// log; `count` is always the true total, so the view can say "200 of 1,204".
const DETAILS_CAP = 200;

// Build the details machinery over a parsed blob.
//
// Everything it cross-references -- which spans a value has, which region a
// block is in, which spans are live at an instruction -- is indexed once here.
// Doing any of it per query is a scan of the whole function per click.
function buildDetails(json, entityEvents) {
  const func = json.function || {};
  const machine = json.machine || {};
  const eventSchema = (json.schema || {}).events || {};

  const blocks = func.blocks || [];
  const insts = func.insts || [];
  const regions = func.regions || [];
  const spans = func.spans || [];
  const bundles = func.bundles || [];
  const uses = func.uses || [];
  const slots = func.spillSlots || [];
  const regs = machine.regs || [];
  const classes = machine.classes || [];
  const banks = machine.banks || [];
  const regGroups = machine.regGroups || [];

  // Values have no array of their own in the blob -- nothing about a value is
  // worth storing that its def, spans and uses do not already say -- so the
  // range check has to come from the highest index anything mentions.
  let valCount = 0;
  const note = (val) => (valCount = Math.max(valCount, val + 1));
  for (const span of spans) note(span.val);
  for (const inst of insts) for (const operand of inst.operands) note(operand.val);
  for (const block of blocks) {
    for (const val of block.params) note(val);
    for (const args of block.callArgs) for (const val of args) note(val);
  }

  // val -> its spans, uses and bundles, all in ascending order.
  const spansOf = group(spans.length, (i) => spans[i].val);
  const usesOf = group(uses.length, (i) => spans[uses[i].span].val);
  const bundlesOf = new Map();
  for (const [val, list] of spansOf) {
    const seen = [];
    for (const i of list) {
      const bundle = spans[i].bundle;
      if (bundle !== null && !seen.includes(bundle)) seen.push(bundle);
    }
    bundlesOf.set(val, seen);
  }

  // val -> where it comes into existence, as parts. An operand or a block
  // parameter; a value with neither is one nothing defines, which is legal
  // input and renders as `none`.
  const defOf = new Map();
  blocks.forEach((block, b) => {
    block.params.forEach((val, i) => {
      if (!defOf.has(val)) defOf.set(val, [entity("Block", b), text(" param " + i)]);
    });
  });
  insts.forEach((inst, i) => {
    inst.operands.forEach((operand) => {
      if (operand.defUse !== "def" || defOf.has(operand.val)) return;
      defOf.set(operand.val, [entity("Inst", i), text(" " + operand.pos)]);
    });
  });

  // block -> the region that owns it, which is what makes an edge "incoming".
  const regionOf = new Map();
  regions.forEach((region, i) => {
    if (region === null) return;
    for (const block of region.blocks) regionOf.set(block, i);
  });

  // inst -> the spans live at either of its points. A span is live during an
  // instruction when it brackets one of them, which includes spans with no use
  // in the instruction at all.
  const spansAt = new Map();
  insts.forEach((_inst, i) => spansAt.set(i, []));
  spans.forEach((span, i) => {
    const from = Math.floor(at(span.start) / 2);
    const to = Math.floor(at(span.end) / 2);
    for (let inst = from; inst <= to; inst++) {
      const list = spansAt.get(inst);
      if (list !== undefined) list.push(i);
    }
  });

  // slot -> the value that lives in it, and the instructions and edges whose
  // edits touch it. Neither is stored: a slot knows only its size.
  const valOfSlot = new Map();
  for (const span of spans) {
    const ref = allocationRef(span.allocation);
    if (ref && ref.kind === "SpillSlot" && !valOfSlot.has(ref.index)) {
      valOfSlot.set(ref.index, span.val);
    }
  }
  const usersOfSlot = new Map();
  const touches = (slot, parts) => {
    const list = usersOfSlot.get(slot);
    if (list === undefined) usersOfSlot.set(slot, [parts]);
    else list.push(parts);
  };
  insts.forEach((inst, i) => {
    for (const edit of inst.edits) {
      for (const slot of editSlots(edit.edit)) touches(slot, [entity("Inst", i)]);
    }
  });
  blocks.forEach((block, b) => {
    for (const edge of block.edgeEdits) {
      for (const slot of editSlots(edge.edit)) {
        touches(slot, [entity("Block", b), text(" edge " + edge.succ)]);
      }
    }
  });

  // group -> its slots, the other direction of `spillSlots[i].group`.
  const slotsOfGroup = group(slots.length, (i) => slots[i].group);

  // The parts for an entity as the other panes spell it.
  const spanParts = (i) => [
    entity("LiveSpan", i),
    text("("),
    ...valueParts(spans[i].val, spans[i].allocation),
    text(")"),
  ];
  const blockWith = (b, vals) => [
    entity("Block", b),
    text("("),
    ...joinParts(vals.map((val) => [entity("Val", val)])),
    text(")"),
  ];
  const edgeParts = (from, to) => [entity("Block", from), text(" -> "), entity("Block", to)];

  // The fields of one entity, or `null` when there is no such entity. A
  // `switch` over the Rust type name: the kind is what the blob's `schema`
  // speaks in, and re-deriving it from a display prefix would be a parser.
  function fieldsOf(ref) {
    const i = ref.index;
    switch (ref.kind) {
      case "Val": {
        if (!inRange(i, valCount)) return null;
        return [
          { label: "Def", value: defOf.get(i) || none() },
          listField("Uses", "Use", usesOf.get(i) || []),
          list("Spans", (spansOf.get(i) || []).map(spanParts), (spansOf.get(i) || []).length),
          listField("Bundles", "LiveBundle", bundlesOf.get(i) || []),
        ];
      }

      case "Block": {
        const block = blocks[i];
        if (block === undefined) return null;
        // The arguments a predecessor passes ride on its own outgoing edge, so
        // each edge has to be found from the other end -- and counted, since a
        // conditional whose arms share a target appears twice in both lists
        // and passes its own arguments along each.
        const nth = new Map();
        const preds = block.predecessors.map((p) => {
          const n = nth.get(p) || 0;
          nth.set(p, n + 1);
          const edges = [];
          blocks[p].successors.forEach((s, e) => s === i && edges.push(e));
          const edge = edges[n];
          return blockWith(p, edge === undefined ? [] : blocks[p].callArgs[edge] || []);
        });
        const succs = block.successors.map((s) => blockWith(s, blocks[s].params));
        return [
          // First, the way `Region`'s own "Parent" field is: where the block
          // sits is what the rest of the pane is relative to.
          {
            label: "Region",
            value: regionOf.has(i) ? [entity("Region", regionOf.get(i))] : none(),
          },
          { label: "Frequency", value: [text(num(block.frequency))] },
          listField("Instructions", "Inst", block.insts),
          list("Predecessors", preds, preds.length),
          list("Successors", succs, succs.length),
          list("Live-in spans", block.liveInSpans.map(spanParts), block.liveInSpans.length),
          list("Live-out spans", block.liveOutSpans.map(spanParts), block.liveOutSpans.length),
        ];
      }

      case "Use": {
        const use = uses[i];
        if (use === undefined) return null;
        const inst = insts[use.point.inst];
        const operand = inst === undefined ? undefined : inst.operands[use.operand];
        return [
          {
            label: "Constraint",
            value: operand === undefined ? none() : constraintParts(operand.constraint),
          },
          { label: "Operand", value: [text(String(use.operand))] },
          { label: "Instruction", value: pointParts(use.point) },
          { label: "Spill weight", value: [text(num(use.weight))] },
        ];
      }

      case "LiveSpan": {
        const span = spans[i];
        if (span === undefined) return null;
        const weight = span.uses.reduce((sum, u) => sum + (uses[u] ? uses[u].weight : 0), 0);
        return [
          { label: "Value", value: [entity("Val", span.val)] },
          { label: "Bundle", value: span.bundle === null ? none() : [entity("LiveBundle", span.bundle)] },
          { label: "Allocation", value: allocationParts(span.allocation) },
          { label: "Constraint", value: constraintParts(span.constraint) },
          // Summed from its uses: weight is recorded per use, because that is
          // where it is earned.
          { label: "Weight", value: [text(num(weight))] },
          { label: "Start", value: pointParts(span.start) },
          { label: "End", value: pointParts(span.end) },
          {
            label: "Split off of",
            value: span.parent === null
              ? none()
              : [entity("LiveSpan", span.parent.parent), text(" at "), ...pointParts(span.parent.at)],
          },
          { label: "Block", value: [entity("Block", span.block)] },
          listField("Uses", "Use", span.uses),
        ];
      }

      case "LiveBundle": {
        const bundle = bundles[i];
        if (bundle === undefined) return null;
        const vals = [];
        for (const s of bundle.spans) if (!vals.includes(spans[s].val)) vals.push(spans[s].val);
        return [
          { label: "Allocation", value: allocationParts(bundle.allocation) },
          { label: "Constraint", value: constraintParts(bundle.constraint) },
          listField("Hint", "Reg", bundle.preference),
          {
            label: "Split off of",
            value: bundle.parent === null ? none() : [entity("LiveBundle", bundle.parent)],
          },
          list("Spans", bundle.spans.map(spanParts), bundle.spans.length),
          listField("Values", "Val", vals),
          { label: "Region", value: [entity("Region", bundle.region)] },
          { label: "Spill weight", value: [text(num(bundle.spillWeight))] },
          { label: "Minimal", value: [text(bundle.isMinimal ? "yes" : "no")] },
        ];
      }

      case "Region": {
        const region = regions[i];
        if (region === undefined || region === null) return null;
        const incoming = [];
        const outgoing = [];
        for (const b of region.blocks) {
          for (const p of blocks[b].predecessors) {
            if (regionOf.get(p) !== i) incoming.push(edgeParts(p, b));
          }
          for (const s of blocks[b].successors) {
            if (regionOf.get(s) !== i) outgoing.push(edgeParts(b, s));
          }
        }
        return [
          { label: "Parent", value: region.parent === null ? none() : [entity("Region", region.parent)] },
          listField("Children", "Region", region.children),
          listField("Blocks", "Block", region.blocks),
          list("Incoming edges", incoming, incoming.length),
          list("Outgoing edges", outgoing, outgoing.length),
          listField("Bundles", "LiveBundle", region.bundles),
          { label: "Depth", value: [text(String(region.depth))] },
        ];
      }

      case "Inst": {
        const inst = insts[i];
        if (inst === undefined) return null;
        const live = spansAt.get(i) || [];
        const operands = inst.operands.map((operand, n) => [
          text(n + ": " + operand.defUse + " " + operand.pos + " "),
          entity("Val", operand.val),
          text(" "),
          ...constraintParts(operand.constraint),
        ]);
        return [
          list("Live spans", live.map(spanParts), live.length),
          { label: "Block", value: [entity("Block", inst.block)] },
          list("Operands", operands, operands.length),
          list("Edits", inst.edits.map((edit) => editParts(edit.edit)), inst.edits.length),
        ];
      }

      case "SpillSlot": {
        const slot = slots[i];
        if (slot === undefined) return null;
        const val = valOfSlot.get(i);
        const users = usersOfSlot.get(i) || [];
        return [
          {
            label: "Value",
            value: slot.emergency
              ? [text("none; an emergency slot, borrowed to break a move cycle")]
              : val === undefined
                ? none()
                : [entity("Val", val)],
          },
          { label: "Size", value: [text(slot.size + (slot.size === 1 ? " byte" : " bytes"))] },
          list("Used by", users, users.length),
          { label: "Group", value: slot.group === null ? none() : [entity("SpillSlotGroup", slot.group)] },
        ];
      }

      case "SpillSlotGroup": {
        const members = slotsOfGroup.get(i);
        if (members === undefined) return null;
        return [listField("Members", "SpillSlot", members)];
      }

      case "Reg": {
        const reg = regs[i];
        if (reg === undefined) return null;
        return [
          { label: "Bank", value: [entity("RegBank", reg.bank)] },
          listField("Classes", "RegClass", reg.classes),
          listField("Groups", "RegGroup", reg.groups),
          { label: "Allocatable", value: [text(reg.allocatable ? "yes" : "no")] },
        ];
      }

      case "RegClass": {
        const cls = classes[i];
        if (cls === undefined) return null;
        // A group class's members are groups; a plain one's are registers.
        // One field either way, because the pane asks the same question.
        return [
          { label: "Bank", value: [entity("RegBank", cls.bank)] },
          cls.isGroup
            ? listField("Members", "RegGroup", cls.groups)
            : listField("Members", "Reg", cls.regs),
          { label: "Spill cost", value: [text(num(cls.spillCost))] },
          { label: "Derived", value: [text(cls.derived ? "yes" : "no")] },
        ];
      }

      case "RegGroup": {
        const regGroup = regGroups[i];
        if (regGroup === undefined) return null;
        return [
          listField("Members", "Reg", regGroup.members),
          { label: "Bank", value: [entity("RegBank", regGroup.bank)] },
        ];
      }

      case "RegBank": {
        const bank = banks[i];
        if (bank === undefined) return null;
        return [
          listField("Registers", "Reg", bank.regs),
          listField("Classes", "RegClass", bank.classes),
          listField("Non-allocatable", "Reg", bank.nonAllocatable),
          { label: "Slot size", value: [text(bank.size + (bank.size === 1 ? " byte" : " bytes"))] },
        ];
      }

      default:
        return null;
    }
  }

  return {
    details(ref) {
      const fields = fieldsOf(ref);
      if (fields === null) return null;
      const indices = entityEvents(ref);
      return {
        ref,
        fields,
        // The true total beside the capped list, like every other list here.
        eventCount: indices.length,
        events: indices.slice(0, DETAILS_CAP).map((i) => eventRow(json.events || [], eventSchema, i)),
      };
    },
  };
}

// Invert a mapping from index to key, dropping `null` keys.
function group(length, keyOf) {
  const out = new Map();
  for (let i = 0; i < length; i++) {
    const key = keyOf(i);
    if (key === null || key === undefined) continue;
    const list = out.get(key);
    if (list === undefined) out.set(key, [i]);
    else list.push(i);
  }
  return out;
}

// A field with no value. Text, not an empty list: an empty field on screen
// reads as a rendering bug rather than as an answer.
const none = () => [text("none")];

const inRange = (index, length) => Number.isInteger(index) && index >= 0 && index < length;

// Parts lists joined by `sep`, flattened into one parts list.
function joinParts(items, sep = ", ") {
  const out = [];
  items.forEach((parts, i) => {
    if (i > 0) out.push(text(sep));
    out.push(...parts);
  });
  return out;
}

// A field holding a list. `count` is the true total and the value is what
// survived the cap, so the two disagree exactly when the list was truncated.
function list(label, items, count) {
  const shown = items.slice(0, DETAILS_CAP);
  const value = count === 0 ? none() : joinParts(shown);
  if (count > shown.length) value.push(text(", …and " + (count - shown.length) + " more"));
  return { label, count, value };
}

const listField = (label, kind, indices) =>
  list(label, indices.map((i) => [entity(kind, i)]), indices.length);

// A float as short as it can be written without lying about it.
const num = (value) => String(Math.round(value * 1e4) / 1e4);

// `inst3:early`, with the instruction clickable.
const pointParts = (point) => [entity("Inst", point.inst), text(":" + point.pos)];

// `any`, `stack`, or `reg rc2`.
const constraintParts = (constraint) =>
  typeof constraint === "string"
    ? [text(constraint)]
    : [text("reg "), entity("RegClass", constraint.reg)];

// The entity an allocation names, as parts.
function allocationParts(allocation) {
  const ref = allocationRef(allocation);
  return ref === null ? none() : [entity(ref.kind, ref.index)];
}

// The spill slots an edit reads or writes.
function editSlots(edit) {
  if (edit.criticalEdge) return editSlots(edit.criticalEdge.edit);
  const move = edit.move;
  if (move && move.spill) return [move.spill.to];
  if (move && move.reload) return [move.reload.from];
  return [];
}

// One event as a single line of parts.
//
// Schema-driven rather than a switch over forty event kinds: the blob's
// `schema.events` already says which field holds which kind of entity, and a
// second list here would be the one that goes stale. Commit 11's event log
// renders events with this same function.
function summarizeEvent(event, eventSchema) {
  const fields = eventSchema[event.kind] || {};
  const parts = [text(event.kind)];
  for (const key of Object.keys(event)) {
    if (key === "kind") continue;
    parts.push(text(" " + key + "="), ...fieldParts(fields[key], event[key]));
  }
  return parts;
}

// One value of an event or a blob record, against the schema descriptor that
// says what it holds. A descriptor is an entity type name, a one-element array
// of one, or an object keyed by field or variant name.
function fieldParts(descriptor, value) {
  if (value === null || value === undefined) return none();
  if (typeof descriptor === "string") return [entity(descriptor, value)];
  if (Array.isArray(descriptor)) {
    if (!Array.isArray(value)) return [text(plain(value))];
    return [text("["), ...joinParts(value.map((v) => fieldParts(descriptor[0], v))), text("]")];
  }
  // A program point is the one shape the schema does not describe -- its
  // instruction is an entity, but a point is not itself one -- so it is
  // recognized structurally.
  if (isPoint(value)) return pointParts(value);
  if (descriptor && typeof value === "object" && !Array.isArray(value)) {
    const keys = Object.keys(value);
    // One key is an enum variant and reads as a prefix; more than one is a
    // struct and reads as its fields.
    if (keys.length === 1) {
      return [text(keys[0] + " "), ...fieldParts(descriptor[keys[0]], value[keys[0]])];
    }
    const inner = keys.map((k) => [text(k + ": "), ...fieldParts(descriptor[k], value[k])]);
    return [text("{"), ...joinParts(inner), text("}")];
  }
  return [text(plain(value))];
}

const isPoint = (value) =>
  value !== null &&
  typeof value === "object" &&
  typeof value.inst === "number" &&
  typeof value.pos === "string" &&
  Object.keys(value).length === 2;

// A value with no entities in it, as text.
const plain = (value) =>
  typeof value === "number"
    ? num(value)
    : typeof value === "string"
      ? value
      : JSON.stringify(value);

// ---------------------------------------------------------------------------
// The event log.

// One event as the log and the details pane both draw it.
const eventRow = (events, eventSchema, index) => ({
  index,
  kind: events[index].kind,
  summary: summarizeEvent(events[index], eventSchema),
});

// Which events match a search.
//
// Two query forms and nothing else: a whole entity label, or a
// case-insensitive substring of an event kind. The spec asks for one term, so
// there is no query language here to invent.
function searchEvents(json, byKind, entityEvents, query) {
  const events = json.events || [];
  // Trimmed, because a trailing space is a typo and not a query, and an
  // entity label with one around it parses as nothing at all.
  const text = String(query === undefined || query === null ? "" : query).trim();
  if (text === "") return events.map((_event, i) => i);

  // `event9` is a position in the log rather than an entity: `EventIndex` is
  // deliberately left out of the prefix table, so `parseEntityLabel` never
  // returns one and there is no `byEntity.EventIndex` to go looking for.
  const eventPrefix = (json.entityKinds || {}).EventIndex;
  if (eventPrefix !== undefined && text.startsWith(eventPrefix)) {
    const rest = text.slice(eventPrefix.length);
    if (/^[0-9]+$/.test(rest)) {
      const i = Number(rest);
      return i < events.length ? [i] : [];
    }
  }

  // An entity label wins. `r3` is a register, and only a query that parses as
  // nothing -- `re`, with no digits -- falls through to matching `Remat`. An
  // entity that exists but appears in no event matches nothing, which is not
  // the same question as "which kinds contain this text".
  const ref = parseEntityLabel(text);
  if (ref !== null) return entityEvents(ref).slice();

  // Matched once per kind rather than once per event, which is what `byKind`
  // is for.
  const needle = text.toLowerCase();
  const found = [];
  for (const [kind, indices] of Object.entries(byKind)) {
    if (kind.toLowerCase().includes(needle)) found.push(...indices);
  }
  // Each kind's list is ascending, but their union is not, and a log out of
  // order is not a log.
  return found.sort((a, b) => a - b);
}

// ---------------------------------------------------------------------------
// The histograms tab.

// The table of contents' groups, in the order it shows them.
//
// Hard-coded, because the grouping is an editorial judgement about what a
// reader wants to see beside what, and nothing in the data expresses it. The
// Rust side asserts the id set it produces (`histogram_ids_are_the_expected_set`
// in `index.rs`) and the tests below assert that every id named here is in it,
// which is the pair that keeps the two from drifting.
const HISTOGRAM_GROUPS = [
  [
    "Control flow",
    [
      "blocks-per-region",
      "region-depth",
      "incoming-edges-per-region",
      "outgoing-edges-per-region",
      "incoming-edges-per-block",
      "outgoing-edges-per-block",
    ],
  ],
  [
    "Liveness",
    [
      "spans-per-value",
      "spans-per-bundle",
      "values-per-bundle",
      "instructions-per-span",
      "instructions-per-bundle",
      "uses-per-span",
      "uses-per-bundle",
      "live-in-values-per-block",
      "live-out-values-per-block",
      "live-in-spans-per-block",
      "live-out-spans-per-block",
    ],
  ],
  [
    "Allocation",
    [
      "bundles-per-region",
      "queue-pops-per-bundle",
      "queue-pops-per-region",
      "evictions-per-bundle",
      "total-splits-per-bundle",
      "within-span-splits-per-bundle",
      "between-span-splits-per-bundle",
    ],
  ],
  ["Spills and moves", ["spills-per-value", "spills-per-bundle", "parallel-moves-per-solve"]],
];

// Group the histograms for the table of contents.
function groupHistograms(histograms) {
  const byId = new Map(histograms.map((histogram) => [histogram.id, histogram]));
  const item = ({ id, title, count }) => ({ id, title, count });
  const groups = [];
  const placed = new Set();
  for (const [group, ids] of HISTOGRAM_GROUPS) {
    const items = [];
    for (const id of ids) {
      const histogram = byId.get(id);
      // A named histogram the blob does not carry is simply absent, not an
      // empty entry pointing at nothing.
      if (histogram === undefined) continue;
      items.push(item(histogram));
      placed.add(id);
    }
    if (items.length > 0) groups.push({ group, items });
  }
  // Whatever the grouping does not name is still shown. A histogram added on
  // the Rust side must not be invisible here just because nobody thought to
  // file it, and a trailing group is how that failure announces itself.
  const rest = histograms.filter((histogram) => !placed.has(histogram.id));
  if (rest.length > 0) groups.push({ group: "Other", items: rest.map(item) });
  return groups;
}

// The grouping's ids, in order, for the tests that keep it honest.
export const histogramGroupIds = () => HISTOGRAM_GROUPS.flatMap(([, ids]) => ids);
