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
  const ref = { kind: "Val", index: 3 };
  assert.deepEqual(createModel({}).details(ref).ref, ref);
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
function outlineOf(blob) {
  installEntities(blob.entityKinds);
  return createModel(blob).functionOutline();
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
