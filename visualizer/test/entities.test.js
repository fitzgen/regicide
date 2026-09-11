import assert from "node:assert/strict";
import test from "node:test";
import * as entities from "../js/entities.js";

// The real table, as `visualizer.rs` emits it.
const KINDS = {
  Val: "v",
  Block: "block",
  Inst: "inst",
  Region: "region",
  LiveSpan: "span",
  LiveBundle: "bundle",
  Use: "use",
  SpillSlot: "stack",
  SpillSlotGroup: "stack_group",
  Reg: "r",
  RegUnit: "unit",
  RegGroup: "group",
  RegClass: "rc",
  RegBank: "bank",
  EventIndex: "event",
};

entities.install(KINDS);

test("entityLabel uses the blob's prefixes", () => {
  assert.equal(entities.entityLabel({ kind: "Val", index: 3 }), "v3");
  assert.equal(entities.entityLabel({ kind: "RegClass", index: 12 }), "rc12");
  assert.equal(entities.entityLabel({ kind: "SpillSlotGroup", index: 0 }), "stack_group0");
});

test("entityKey and entityLabel round-trip through parseEntityLabel", () => {
  for (const kind of Object.keys(KINDS)) {
    if (kind === "EventIndex") continue;
    const ref = { kind, index: 7 };
    assert.deepEqual(entities.parseEntityLabel(entities.entityLabel(ref)), ref);
    assert.equal(entities.entityKey(ref), kind + ":7");
  }
});

test("parseEntityLabel takes the longest matching prefix", () => {
  // The prefixes are not disjoint: "r" is a prefix of "rc", "region" starts
  // with "r", and "stack" is a prefix of "stack_group".
  assert.deepEqual(entities.parseEntityLabel("rc12"), { kind: "RegClass", index: 12 });
  assert.deepEqual(entities.parseEntityLabel("region5"), { kind: "Region", index: 5 });
  assert.deepEqual(entities.parseEntityLabel("r3"), { kind: "Reg", index: 3 });
  assert.deepEqual(entities.parseEntityLabel("group1"), { kind: "RegGroup", index: 1 });
  assert.deepEqual(entities.parseEntityLabel("stack2"), { kind: "SpillSlot", index: 2 });
  assert.deepEqual(entities.parseEntityLabel("stack_group2"), {
    kind: "SpillSlotGroup",
    index: 2,
  });
  assert.deepEqual(entities.parseEntityLabel("v10"), { kind: "Val", index: 10 });
});

test("parseEntityLabel rejects everything else", () => {
  for (const text of ["rc", "v", "v3x", "", "3", "nope7", "reg_group1", "v-1"]) {
    assert.equal(entities.parseEntityLabel(text), null, text);
  }
  // An event is a log position, not an entity: it has no `byEntity` list and
  // commit 11 parses it separately.
  assert.equal(entities.parseEntityLabel("event9"), null);
});

test("sameEntity compares structurally", () => {
  assert.ok(entities.sameEntity({ kind: "Val", index: 1 }, { kind: "Val", index: 1 }));
  assert.ok(!entities.sameEntity({ kind: "Val", index: 1 }, { kind: "Val", index: 2 }));
  assert.ok(!entities.sameEntity({ kind: "Val", index: 1 }, { kind: "Block", index: 1 }));
  assert.ok(!entities.sameEntity(null, { kind: "Val", index: 1 }));
  assert.ok(!entities.sameEntity(null, null));
});

test("bundleColor stays inside the ramp", () => {
  for (let i = 0; i < 3 * entities.BUNDLE_RAMP_LENGTH; i++) {
    const color = entities.bundleColor(i);
    assert.match(color, /^var\(--bundle-[0-7]\)$/);
    assert.equal(color, entities.bundleColor(i % entities.BUNDLE_RAMP_LENGTH));
  }
});
