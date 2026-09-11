//! The type table: what the bare integers in the blob mean.
//!
//! Entities serialize as bare indices, so nothing in the JSON says whether a
//! `3` is a value, a block, or a register. This table says, field by field,
//! and it is the only place entity *types* appear in the blob.

use serde::ser::{SerializeMap, SerializeSeq as _};

/// What one field holds.
///
/// Exactly three forms, and the JavaScript walks them recursively:
///
/// * [`Descriptor::Entity`] is an entity type's name, and the value under it
///   is that entity's index;
/// * [`Descriptor::List`] is an array of whatever it wraps;
/// * [`Descriptor::Fields`] is an object, which covers both a struct and a
///   tagged union, because the two are traversed identically: recurse into
///   whichever keys are present.
///
/// A field that holds no entity — an ordinal, a count, a point, a weight —
/// has no descriptor at all and is simply absent.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Descriptor {
    /// An entity index, under the named entity type.
    Entity(&'static str),

    /// An array of what it wraps.
    List(&'static Descriptor),

    /// An object, keyed by field name or by variant tag.
    Fields(&'static [(&'static str, Descriptor)]),
}

impl serde::Serialize for Descriptor {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Entity(kind) => serializer.serialize_str(kind),
            Self::List(inner) => {
                let mut seq = serializer.serialize_seq(Some(1))?;
                seq.serialize_element(inner)?;
                seq.end()
            }
            Self::Fields(fields) => {
                let mut map = serializer.serialize_map(Some(fields.len()))?;
                for (name, descriptor) in *fields {
                    map.serialize_entry(name, descriptor)?;
                }
                map.end()
            }
        }
    }
}

impl Descriptor {
    /// Call `f` with every entity type name this descriptor mentions.
    ///
    /// Only the exhaustiveness test walks the table; the page reads it as
    /// JSON.
    #[cfg(test)]
    pub(crate) fn visit_kinds(&self, f: &mut impl FnMut(&'static str)) {
        match self {
            Self::Entity(kind) => f(kind),
            Self::List(inner) => inner.visit_kinds(f),
            Self::Fields(fields) => {
                for (_, descriptor) in *fields {
                    descriptor.visit_kinds(f);
                }
            }
        }
    }
}

/// The fields of one struct or one event variant.
///
/// A field with no descriptor names no entity; it is listed anyway so that
/// adding one to an event is a compile error here, and skipped when the table
/// is written out.
pub(crate) type Fields = &'static [(&'static str, Option<Descriptor>)];

/// A table of named field sets: the `events` half is keyed by event kind, the
/// `function` and `machine` halves by struct name.
pub(crate) type Table = &'static [(&'static str, Fields)];

/// Serializes a [`Table`] as a plain object, skipping the fields that name no
/// entity.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SerializeTable(pub(crate) Table);

impl serde::Serialize for SerializeTable {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.0.len()))?;
        for (name, fields) in self.0 {
            map.serialize_entry(name, &SerializeFields(fields))?;
        }
        map.end()
    }
}

/// Serializes one [`Fields`] as an object of the fields that have a
/// descriptor.
struct SerializeFields<'a>(&'a Fields);

impl serde::Serialize for SerializeFields<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        for (name, descriptor) in *self.0 {
            if let Some(descriptor) = descriptor {
                map.serialize_entry(name, descriptor)?;
            }
        }
        map.end()
    }
}

/// Call `f` with every entity type name `table` mentions.
#[cfg(test)]
pub(crate) fn visit_table_kinds(table: Table, f: &mut impl FnMut(&'static str)) {
    for (_, fields) in table {
        for (_, descriptor) in *fields {
            if let Some(descriptor) = descriptor {
                descriptor.visit_kinds(f);
            }
        }
    }
}

use Descriptor::{Entity, Fields as Obj, List};

/// An [`crate::input::OperandConstraint`]: only its `Reg` variant names one.
pub(crate) const CONSTRAINT: Descriptor = Obj(&[("reg", Entity("RegClass"))]);

/// A [`crate::machine::RegSet`], which serializes as its members.
pub(crate) const REG_SET: Descriptor = List(&Entity("Reg"));

/// A [`crate::output::RegAllocation`].
pub(crate) const REG_ALLOCATION: Descriptor =
    Obj(&[("reg", Entity("Reg")), ("regGroup", Entity("RegGroup"))]);

/// A [`crate::output::StackAllocation`].
pub(crate) const STACK_ALLOCATION: Descriptor = Obj(&[
    ("slot", Entity("SpillSlot")),
    ("slotGroup", Entity("SpillSlotGroup")),
]);

/// A [`crate::output::Allocation`], which flattens the two above.
pub(crate) const ALLOCATION: Descriptor = Obj(&[
    ("reg", Entity("Reg")),
    ("regGroup", Entity("RegGroup")),
    ("slot", Entity("SpillSlot")),
    ("slotGroup", Entity("SpillSlotGroup")),
]);

/// A [`crate::output::ScalarAllocation`].
pub(crate) const SCALAR_ALLOCATION: Descriptor =
    Obj(&[("reg", Entity("Reg")), ("slot", Entity("SpillSlot"))]);

/// A [`crate::parallel_moves::ParallelMove`].
pub(crate) const PARALLEL_MOVE: Descriptor =
    Obj(&[("src", SCALAR_ALLOCATION), ("dst", SCALAR_ALLOCATION)]);

/// A [`crate::output::Move`].
pub(crate) const MOVE: Descriptor = Obj(&[
    (
        "regReg",
        Obj(&[("from", Entity("Reg")), ("to", Entity("Reg"))]),
    ),
    (
        "spill",
        Obj(&[("from", Entity("Reg")), ("to", Entity("SpillSlot"))]),
    ),
    (
        "reload",
        Obj(&[("from", Entity("SpillSlot")), ("to", Entity("Reg"))]),
    ),
]);

/// A [`crate::output::Remat`].
pub(crate) const REMAT: Descriptor = Obj(&[("val", Entity("Val")), ("dest", Entity("Reg"))]);

/// A [`crate::output::EdgeEdit`].
pub(crate) const EDGE_EDIT: Descriptor = Obj(&[("move", MOVE), ("remat", REMAT)]);

/// A [`crate::output::Edit`].
///
/// A critical edge's `succ` is a successor ordinal, not a block, and so is
/// deliberately absent: typing it would make the page render `block1`.
pub(crate) const EDIT: Descriptor = Obj(&[
    ("move", MOVE),
    ("remat", REMAT),
    (
        "criticalEdge",
        Obj(&[("target", Entity("Block")), ("edit", EDGE_EDIT)]),
    ),
]);

/// A [`crate::move_generation::MovePosition`]: a point names no entity of its
/// own, and an edge's `succ` is an ordinal.
pub(crate) const MOVE_POSITION: Descriptor =
    Obj(&[("criticalEdge", Obj(&[("pred", Entity("Block"))]))]);
