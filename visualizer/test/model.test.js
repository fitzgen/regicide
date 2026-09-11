import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { createModel } from "../js/model.js";
import { entityClass, entityLabel, installEntities } from "../js/entities.js";

test("createModel answers the documented queries", () => {
  const model = createModel({});
  for (const method of [
    "details",
    "searchEvents",
    "functionOutline",
    "histograms",
    "event",
    "entity",
  ]) {
    assert.equal(typeof model[method], "function", method);
  }
});

test("a details result carries its own ref back", () => {
  // The main thread caches a result by `entityKey(result.ref)`, so the result
  // has to say which entity it is for; nothing else in it does.
  const ref = { kind: "Val", index: 1 };
  assert.deepEqual(modelOf(fixture("spills-and-reloads")).details(ref).ref, ref);
});

test("a SecondaryMap read past the end of `values` is the default", () => {
  // `values` stops at the highest key ever written, so the tail of the entity
  // space is only covered by `default`.
  const model = createModel({
    entityKinds: { Val: "v" },
    index: { byEntity: { Val: { default: [], values: [[0, 2], [1]] } } },
  });
  assert.deepEqual(model.entity({ kind: "Val", index: 0 }).events, [0, 2]);
  assert.deepEqual(model.entity({ kind: "Val", index: 1 }).events, [1]);
  assert.deepEqual(model.entity({ kind: "Val", index: 99 }).events, []);
});

test("a kind with no index of its own reads as no events", () => {
  // `RegUnit` and `RegBank` are entity kinds but nothing indexes them.
  const model = createModel({ entityKinds: { RegUnit: "unit" }, index: { byEntity: {} } });
  assert.deepEqual(model.entity({ kind: "RegUnit", index: 0 }).events, []);
});

// The fixtures the Rust side regenerates and diffs on every `cargo test`. A
// blob written here instead would drift from the Rust shape silently.
function fixture(name) {
  const path = new URL("./fixtures/" + name + ".json", import.meta.url);
  return JSON.parse(readFileSync(path, "utf8"));
}

// A model over a fixture, with the fixture's prefixes installed. `entityLabel`
// is process-global, so every test that renders has to do this.
function modelOf(blob) {
  installEntities(blob.entityKinds);
  return createModel(blob);
}

function outlineOf(blob) {
  return modelOf(blob).functionOutline();
}

// The lines rendered back to the text the spec describes. `view.js` indents by
// the same `depth * 4`.
function render(outline) {
  return outline.lines.map((line) => " ".repeat(line.depth * 4) + text(line)).join("\n");
}

const text = (line) => line.parts.map((part) => part.text).join("");

test("the outline renders the shape the spec describes", () => {
  // The highest-value assertion on the web side: nesting, the `early:`/`late:`
  // column, edits around the point they happen at, edge lines with their
  // arguments, and the critical edge's edit indented under the edge it is on.
  assert.equal(
    render(outlineOf(fixture("critical-edge"))),
    [
      "function {",
      "    region2 {",
      "        entry block0:",
      "            inst0 early:",
      "                   late: def v0[r1]",
      "            inst1 early: use v0[r1]",
      "                   late:",
      "            inst2 early:",
      "                   late:",
      "                --> block1",
      "                --> block2(v0[r1])",
      "                    move r1 to r0",
      "",
      "        block1:",
      "            move r1 to r0",
      "            inst3 early:",
      "                   late: def v1[r1]",
      "            inst4 early: use v0[r0]",
      "                   late:",
      "            inst5 early:",
      "                   late:",
      "                --> block2(v0[r0])",
      "",
      "        block2(v2[r0]):",
      "            inst6 early: use v2[r0]",
      "                   late:",
      "            inst7 early:",
      "                   late:",
      "                --> returns",
      "    }",
      "}",
    ].join("\n"),
  );
});

test("a single-block function renders its slots and its return", () => {
  // One block, one region, no edges: the case most likely to come out as a
  // stray brace pair. Also the only fixture with two spill slots, and so the
  // only one that can show the singular `byte`.
  assert.equal(
    render(outlineOf(fixture("spills-and-reloads"))),
    [
      "function {",
      "    stack0: 8 bytes",
      "    stack1: 1 byte",
      "",
      "    region0 {",
      "        entry block0:",
      "            inst0 early:",
      "                   late: def v0[r1]",
      "            move r1 to stack0",
      "            inst1 early:",
      "                   late: def v1[r4]",
      "            move r4 to stack1",
      "            inst2 early: use v0[stack0], use v1[stack1]",
      "                   late:",
      "            move stack1 to r4",
      "            move stack0 to r1",
      "            inst3 early: use v0[r1], use v1[r4]",
      "                   late:",
      "            inst4 early:",
      "                   late:",
      "                --> returns",
      "    }",
      "}",
    ].join("\n"),
  );
});

test("a block is prefixed by what the embedder called it", () => {
  // `block-kinds` exists for this: the embedder marked one block cold, one
  // hot, and one with a frequency that is neither.
  const prefixes = outlineOf(fixture("block-kinds"))
    .lines.filter((line) => line.kind === "block")
    .map((line) => text(line));
  assert.deepEqual(prefixes, [
    "entry block0:",
    "cold block1:",
    "hot block2:",
    "freq(0.5) block3(v1[r0]):",
  ]);

  // And a block the embedder said nothing about gets no prefix at all.
  const plain = outlineOf(fixture("critical-edge"))
    .lines.filter((line) => line.kind === "block")
    .map((line) => text(line));
  assert.deepEqual(plain, ["entry block0:", "block1:", "block2(v2[r0]):"]);
});

test("a value with nowhere to be is drawn bare", () => {
  // A span that reached no bundle has no allocation, and then there is no
  // `[r1]` to draw. Stripping one span's allocation is how to see it: every
  // span in every fixture got one.
  const blob = fixture("spilled-merge-param");
  blob.function.spans[3].allocation = null;
  const lines = render(outlineOf(blob)).split("\n");

  assert.ok(lines.includes("        block3(v1):"), "the block parameter lost its brackets");
  assert.ok(lines.includes("            inst4 early: use v1"), "the operand lost its brackets");
  // Only that span: the value's other span still says where it is.
  assert.ok(lines.includes("            inst5 early: use v1[stack0]"), "the other span changed");
  assert.ok(lines.includes("                   late: def v0[r0]"), "an unrelated value changed");
});

test("only a critical edge's edits are indented under an edge", () => {
  const outline = outlineOf(fixture("critical-edge"));
  for (const line of outline.lines) {
    const previous = outline.lines[line.row - 1];
    if (line.kind !== "edge-edit") continue;
    assert.equal(previous.kind, "edge", "an edge edit that is not under an edge");
    assert.equal(line.depth, previous.depth + 1, "an edge edit at the wrong depth");
  }
  // The other edits sit at their block's depth, beside the instruction they
  // happen at, not under anything.
  const depths = new Set(
    outline.lines.filter((line) => line.kind === "edit").map((line) => line.depth),
  );
  const insts = new Set(
    outline.lines.filter((line) => line.kind === "inst").map((line) => line.depth),
  );
  assert.deepEqual([...depths], [...insts]);
});

test("both halves of an instruction are drawn, empty or not", () => {
  const outline = outlineOf(fixture("critical-edge"));
  const insts = outline.lines.filter((line) => line.kind === "inst");
  // Two lines each, and the fixture has some of every combination.
  assert.equal(insts.length, 2 * fixture("critical-edge").function.insts.length);
  assert.ok(insts.some((line) => text(line).endsWith(" late:")));
  assert.ok(insts.some((line) => text(line).endsWith(" early:")));
});

test("bars share a column only when they do not overlap", () => {
  const { bars } = outlineOf(fixture("spills-and-reloads"));
  for (const a of bars) {
    for (const b of bars) {
      if (a === b || a.column !== b.column) continue;
      assert.ok(
        a.endRow < b.startRow || b.endRow < a.startRow,
        a.label + " and " + b.label + " overlap in column " + a.column,
      );
    }
  }
  // And the packing is not one column each: the fixture has a span that ends
  // before a later one begins.
  const columns = new Set(bars.map((bar) => bar.column));
  assert.ok(columns.size < bars.length, "no column was reused");
});

test("every entity a line names is a real one, labeled by `entities.js`", () => {
  for (const name of ["spills-and-reloads", "critical-edge", "spilled-merge-param"]) {
    const blob = fixture(name);
    // The kinds the blob carries an array for. `Val`, `RegUnit` and
    // `SpillSlotGroup` are entity kinds with no table of their own.
    const arrays = {
      Block: blob.function.blocks,
      Inst: blob.function.insts,
      Region: blob.function.regions,
      LiveSpan: blob.function.spans,
      LiveBundle: blob.function.bundles,
      SpillSlot: blob.function.spillSlots,
      Use: blob.function.uses,
      Reg: blob.machine.regs,
      RegClass: blob.machine.classes,
      RegBank: blob.machine.banks,
      RegGroup: blob.machine.regGroups,
    };
    const outline = outlineOf(blob);
    let seen = 0;
    for (const line of outline.lines) {
      for (const part of line.parts) {
        if (part.entity === undefined) continue;
        seen += 1;
        const ref = part.entity;
        assert.ok(blob.entityKinds[ref.kind] !== undefined, name + ": unknown kind " + ref.kind);
        assert.ok(Number.isInteger(ref.index) && ref.index >= 0, name + ": bad index");
        const array = arrays[ref.kind];
        if (array) assert.ok(ref.index < array.length, name + ": " + entityLabel(ref) + " is past");
        // Never hand-built: one function decides how an entity reads.
        assert.equal(part.text, entityLabel(ref), name + ": a hand-built label");
        assert.equal(part.cls, entityClass(ref), name + ": a hand-built class");
      }
    }
    assert.ok(seen > 0, name + ": no entities at all");
  }
});

// ---------------------------------------------------------------------------
// The details pane.

// One field's value as text, for the assertions that care what a pane says
// rather than which entities it names.
const flat = (parts) => parts.map((part) => part.text).join("");

// A pane as a `label: value` table, which is how it reads on screen.
const shown = (details) =>
  Object.fromEntries(details.fields.map((field) => [field.label, flat(field.value)]));

const labels = (details) => details.fields.map((field) => field.label);

// The spec's checklist, encoded: every entity kind's fields, in the order the
// pane must show them. Someone reading a pane twice should find the same field
// in the same place, which is exactly what a reordering here would break.
const FIELDS = {
  Val: ["Def", "Uses", "Spans", "Bundles"],
  Block: [
    "Frequency",
    "Instructions",
    "Predecessors",
    "Successors",
    "Live-in spans",
    "Live-out spans",
  ],
  Inst: ["Live spans", "Block", "Operands", "Edits"],
  Use: ["Constraint", "Operand", "Instruction", "Spill weight"],
  LiveSpan: [
    "Value",
    "Bundle",
    "Allocation",
    "Constraint",
    "Weight",
    "Start",
    "End",
    "Split off of",
    "Block",
    "Uses",
  ],
  LiveBundle: [
    "Allocation",
    "Constraint",
    "Hint",
    "Split off of",
    "Spans",
    "Values",
    "Region",
    "Spill weight",
    "Minimal",
  ],
  Region: ["Parent", "Children", "Blocks", "Incoming edges", "Outgoing edges", "Bundles", "Depth"],
  SpillSlot: ["Value", "Size", "Used by", "Group"],
  SpillSlotGroup: ["Members"],
  Reg: ["Bank", "Classes", "Groups", "Allocatable"],
  RegClass: ["Bank", "Members", "Spill cost", "Derived"],
  RegGroup: ["Members", "Bank"],
  RegBank: ["Registers", "Classes", "Non-allocatable", "Slot size"],
};

for (const [kind, expected] of Object.entries(FIELDS)) {
  test("a " + kind + " pane has the spec's fields, in the spec's order", () => {
    const blob = fixture("spills-and-reloads");
    // Slot groups are the one shape no `TestInput` in the crate produces. A
    // perturbation of a real, Rust-written blob beats hand-writing one, and it
    // is only the back-reference that is being checked here.
    blob.function.spillSlots[0].group = 0;
    const details = modelOf(blob).details({ kind, index: 0 });
    assert.ok(details, "no " + kind + " 0 in the fixture");
    assert.deepEqual(labels(details), expected);
    for (const field of details.fields) {
      // A field that renders as nothing looks like a rendering bug on screen,
      // so an absent value is the word `none` and never an empty list.
      assert.ok(field.value.length > 0, kind + "'s " + field.label + " is blank");
    }
    assert.equal(typeof details.eventCount, "number");
  });
}

test("a value's pane names where it comes from and everywhere it lives", () => {
  const details = modelOf(fixture("spills-and-reloads")).details({ kind: "Val", index: 0 });
  assert.deepEqual(shown(details), {
    Def: "inst0 late",
    Uses: "use3, use4, use5",
    Spans: "span0(v0[r1]), span2(v0[stack0]), span4(v0[r1])",
    Bundles: "bundle0, bundle2, bundle4",
  });
});

test("a block's predecessors carry their arguments and its successors their parameters", () => {
  // The two halves of a block call are recorded at opposite ends -- the
  // arguments on the predecessor's outgoing edge, the parameters on the
  // successor -- so each list has to be read from the other block.
  const model = modelOf(fixture("critical-edge"));
  assert.deepEqual(shown(model.details({ kind: "Block", index: 2 })), {
    Frequency: "1",
    Instructions: "inst6, inst7",
    Predecessors: "block0(v0), block1(v0)",
    Successors: "none",
    "Live-in spans": "span3(v2[r0])",
    "Live-out spans": "none",
  });
  assert.equal(shown(model.details({ kind: "Block", index: 0 })).Successors, "block1(), block2(v2)");
});

test("a span reports the span it was split off of, and the point it was cut at", () => {
  // No `TestInput` in the crate splits a span, so the parent is grafted onto a
  // real blob: the field is a straight read, and what is being checked is that
  // both halves of it are shown and that an unsplit span says none.
  const blob = fixture("spills-and-reloads");
  assert.equal(shown(modelOf(blob).details({ kind: "LiveSpan", index: 1 }))["Split off of"], "none");

  blob.function.spans[1].parent = { parent: 0, at: { inst: 2, pos: "early" } };
  const split = modelOf(blob).details({ kind: "LiveSpan", index: 1 });
  assert.equal(shown(split)["Split off of"], "span0 at inst2:early");
  assert.deepEqual(
    split.fields.find((field) => field.label === "Split off of").value.filter((p) => p.entity),
    [
      { text: "span0", entity: { kind: "LiveSpan", index: 0 }, cls: "kind-LiveSpan" },
      { text: "inst2", entity: { kind: "Inst", index: 2 }, cls: "kind-Inst" },
    ],
    "the parent and the split point are both clickable",
  );
});

test("a bundle reports the bundle it was split off of", () => {
  const blob = fixture("spills-and-reloads");
  assert.equal(shown(modelOf(blob).details({ kind: "LiveBundle", index: 1 }))["Split off of"], "none");
  blob.function.bundles[1].parent = 0;
  const split = modelOf(blob).details({ kind: "LiveBundle", index: 1 });
  assert.equal(shown(split)["Split off of"], "bundle0");
});

test("a region's edges are the ones that leave or enter it", () => {
  // The fixtures' regions each hold a whole function, so the region tree is
  // cut in two here: block2 into a child region, the rest left in the parent.
  // An edge is incoming when its predecessor is outside, which is only
  // testable once some block is.
  const blob = fixture("critical-edge");
  blob.function.regions[2] = { ...blob.function.regions[2], blocks: [0, 1], children: [3] };
  blob.function.regions[3] = { blocks: [2], bundles: [], children: [], depth: 1, parent: 2 };
  const model = modelOf(blob);

  assert.deepEqual(shown(model.details({ kind: "Region", index: 3 })), {
    Parent: "region2",
    Children: "none",
    Blocks: "block2",
    // block0 and block1 both jump here, and both are outside now.
    "Incoming edges": "block0 -> block2, block1 -> block2",
    "Outgoing edges": "none",
    Bundles: "none",
    Depth: "1",
  });

  const parent = shown(model.details({ kind: "Region", index: 2 }));
  assert.equal(parent.Children, "region3");
  // block0 -> block1 stays inside, so it is neither.
  assert.equal(parent["Incoming edges"], "none");
  assert.equal(parent["Outgoing edges"], "block0 -> block2, block1 -> block2");
});

test("an instruction lists every span live across it, used there or not", () => {
  // The point of the field: a span that merely covers the instruction is what
  // makes a register unavailable, and a list of the instruction's own operands
  // would not mention it.
  const blob = fixture("spills-and-reloads");
  const details = modelOf(blob).details({ kind: "Inst", index: 1 });
  assert.deepEqual(shown(details)["Live spans"], "span0(v0[r1]), span1(v1[r4])");

  // span0 is live across inst1 and has no use in it.
  const span0 = blob.function.spans[0];
  assert.deepEqual([span0.start, span0.end], [
    { inst: 0, pos: "late" },
    { inst: 2, pos: "early" },
  ]);
  for (const use of span0.uses) assert.notEqual(blob.function.uses[use].point.inst, 1);

  // And the count is the list's length, not the instruction's operand count.
  const field = details.fields.find((f) => f.label === "Live spans");
  assert.equal(field.count, 2);
  assert.equal(blob.function.insts[1].operands.length, 1);
});

test("an emergency slot says so and has no value of its own", () => {
  // An emergency slot is borrowed to break a move cycle; no value has a home
  // in it, which is a thing to say rather than a blank field.
  const blob = fixture("spills-and-reloads");
  blob.function.spillSlots.push({ emergency: true, group: null, size: 8 });
  const details = modelOf(blob).details({ kind: "SpillSlot", index: 2 });
  assert.equal(
    shown(details).Value,
    "none; an emergency slot, borrowed to break a move cycle",
  );
  assert.deepEqual(
    details.fields[0].value.filter((part) => part.entity),
    [],
    "an emergency slot named a value anyway",
  );
});

test("a slot's pane names the instructions and edges whose edits touch it", () => {
  // Nothing in the blob records this: a slot knows its size and its group, and
  // the edits that spill into it or reload out of it are on the other side.
  const model = modelOf(fixture("spills-and-reloads"));
  assert.deepEqual(shown(model.details({ kind: "SpillSlot", index: 0 })), {
    Value: "v0",
    Size: "8 bytes",
    "Used by": "inst1, inst3",
    Group: "none",
  });

  // And an edge's edit counts as a user, named by the edge it sits on.
  const edges = fixture("critical-edge");
  edges.function.blocks[0].edgeEdits[0].edit.criticalEdge.edit = {
    move: { spill: { from: 1, to: 0 } },
  };
  edges.function.spillSlots = [{ emergency: false, group: null, size: 8 }];
  assert.equal(
    shown(modelOf(edges).details({ kind: "SpillSlot", index: 0 }))["Used by"],
    "block0 edge 1",
  );
});

test("a register's pane names its bank and classes, and the events that touched it", () => {
  const blob = fixture("spills-and-reloads");
  const details = modelOf(blob).details({ kind: "Reg", index: 1 });
  assert.deepEqual(shown(details), {
    Bank: "bank0",
    Classes: "rc0, rc2, rc3",
    Groups: "group0",
    Allocatable: "yes",
  });
  // The events are the reason this query is asynchronous, so a register that
  // the allocator actually used must come back with the ones that say so.
  assert.ok(details.eventCount > 0, "r1 was allocated and no event mentions it");
  const kinds = new Set(details.events.map((event) => event.kind));
  assert.ok(
    [...kinds].some((kind) => kind.startsWith("BundleAssigned")),
    "no assignment among " + [...kinds].join(", "),
  );
  for (const event of details.events) {
    assert.equal(typeof event.index, "number");
    assert.equal(blob.events[event.index].kind, event.kind);
    assert.ok(flat(event.summary).startsWith(event.kind), "a summary that hides its kind");
  }
});

test("an event summary names its entities as clickable parts", () => {
  // Written once and reused by commit 11's event log: the two panes must not
  // render the same event differently, so the summary comes from the model.
  const blob = fixture("spills-and-reloads");
  const model = modelOf(blob);
  const found = model
    .details({ kind: "LiveSpan", index: 0 })
    .events.find((event) => event.kind === "SpillPlaced");
  assert.ok(found, "the fixture spills and no SpillPlaced event reached the span");
  assert.equal(
    flat(found.summary),
    "SpillPlaced at=inst1:early block=block0 slot=slot stack0 span=span0 val=v0",
  );
  assert.deepEqual(
    found.summary.filter((part) => part.entity).map((part) => part.entity),
    [
      { kind: "Inst", index: 1 },
      { kind: "Block", index: 0 },
      { kind: "SpillSlot", index: 0 },
      { kind: "LiveSpan", index: 0 },
      { kind: "Val", index: 0 },
    ],
  );
});

test("a list's count is the true total and its value is what survived the cap", () => {
  // The pane says "200 of 1204", so the two disagree exactly when a list was
  // truncated. Anything reading `value.length` as the total is wrong.
  const blob = fixture("spills-and-reloads");
  const inst = blob.function.insts.length - 1;
  const spans = blob.function.spans;
  const original = spans.length;
  // 300 spans live across the last instruction: more than the cap, from a real
  // span copied rather than invented.
  for (let i = 0; i < 300; i++) spans.push({ ...spans[0], start: { inst: 0, pos: "early" }, end: { inst, pos: "late" } });

  const field = modelOf(blob)
    .details({ kind: "Inst", index: inst })
    .fields.find((f) => f.label === "Live spans");
  assert.equal(field.count, 300 + spans.slice(0, original).filter((s) => s.end.inst >= inst).length);
  assert.ok(field.count > 200, "the fixture was not perturbed enough to truncate");
  // Each entry is a span and the value and register inside its label, so it
  // is the spans that are counted.
  const listed = field.value.filter((part) => part.entity && part.entity.kind === "LiveSpan");
  assert.equal(listed.length, 200, "the list was not capped");
  assert.equal(flat(field.value).endsWith(", …and " + (field.count - 200) + " more"), true);
});

test("an entity's event list is capped the same way", () => {
  const blob = fixture("spills-and-reloads");
  const target = blob.events.findIndex((event) => event.kind === "SpillPlaced");
  const map = blob.index.byEntity.LiveSpan;
  // One span named by far more events than the pane will show.
  map.values[0] = Array.from({ length: 250 }, () => target);
  const details = modelOf(blob).details({ kind: "LiveSpan", index: 0 });
  assert.equal(details.eventCount, 250);
  assert.equal(details.events.length, 200);
});

test("details() on nothing at all is null, not a throw", () => {
  const model = modelOf(fixture("spills-and-reloads"));
  const past = {
    Val: 2,
    Block: 1,
    Inst: 5,
    Use: 6,
    LiveSpan: 6,
    LiveBundle: 6,
    Region: 1,
    SpillSlot: 2,
    SpillSlotGroup: 0,
    Reg: 6,
    RegClass: 5,
    RegBank: 2,
    RegGroup: 2,
  };
  for (const [kind, index] of Object.entries(past)) {
    assert.equal(model.details({ kind, index }), null, kind + index + " answered");
    assert.equal(model.details({ kind, index: -1 }), null, kind + " -1 answered");
    assert.equal(model.details({ kind, index: index + 1000 }), null, kind + " far past answered");
  }
  // Kinds with no table of their own, and a kind that is not one at all.
  for (const kind of ["RegUnit", "EventIndex", "Nonsense"]) {
    assert.equal(model.details({ kind, index: 0 }), null, kind + " answered");
  }
});

test("every entity every pane names is a real one, labeled by `entities.js`", () => {
  // The sweep: every field of every entity in every fixture. A part whose ref
  // is out of range is a dead link, and `details` returning null for it is
  // exactly what the pane would hit when the user clicked.
  for (const name of ["spills-and-reloads", "critical-edge", "spilled-merge-param", "block-kinds"]) {
    const blob = fixture(name);
    const model = modelOf(blob);
    let panes = 0;
    let links = 0;
    for (const kind of Object.keys(blob.entityKinds)) {
      for (let index = 0; ; index++) {
        const details = model.details({ kind, index });
        // A sparse table -- `regions` has holes -- so keep going past a gap
        // until the indices are plainly past the end.
        if (!details) {
          if (index > 40) break;
          continue;
        }
        panes += 1;
        assert.deepEqual(details.ref, { kind, index });
        for (const field of details.fields) {
          for (const part of field.value) {
            if (part.entity === undefined) continue;
            links += 1;
            const ref = part.entity;
            const where = name + " " + entityLabel(details.ref) + "." + field.label;
            // Never hand-built: one function decides how an entity reads.
            assert.equal(part.text, entityLabel(ref), where + ": a hand-built label");
            assert.equal(part.cls, entityClass(ref), where + ": a hand-built class");
            assert.ok(Number.isInteger(ref.index) && ref.index >= 0, where + ": bad index");
            assert.ok(model.details(ref) !== null, where + ": " + entityLabel(ref) + " has no pane");
          }
        }
      }
    }
    assert.ok(panes > 10, name + ": only " + panes + " panes");
    assert.ok(links > 10, name + ": only " + links + " links");
  }
});
