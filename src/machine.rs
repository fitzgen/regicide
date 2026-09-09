//! The machine model.
//!
//! This module describes how we model a target machine and its registers. How
//! we model the machine, and what we choose to omit, has direct effects on code
//! quality and hardware "feature" support. For example, without some form of
//! modeling register groups, which can be allocated together and checked for
//! interference against both a single register or another register group, we
//! cannot support:
//!
//! * arm32's `ldrd` (which operates on even-aligned pairs of registers),
//! * aarch64's `ld4` (which operates on a range of four contiguous registers), or
//! * s390x's pervasive use register ranges and pairs.
//!
//! Likewise, without modeling overlapping registers and/or register classes, we
//! couldn't support allocating `ah` and `al` separately from `ax` and `eax` on
//! x86 and x86-64.
//!
//! Our machine model should support:
//!
//! 1. Disjoint register banks.
//!
//!    In practice, every ISA has disjoint register banks, e.g. one for floats
//!    and one for general-purpose registers.
//!
//! 2. Naming "non-allocatable" registers.
//!
//!    Even if the register allocator doesn't "own" a register, it should still
//!    be able to name it, so that special instructions can read from or write
//!    to it. The stack pointer register, for example, usually falls into this
//!    bucket, as does the link register when present in the ISA.
//!
//! 3. A large register index space.
//!
//!    x86-64 has up to 72 registers: 32 GPRs with APX, 32 vector registers with
//!    AVX-512, and 8 mask registers with AVX-512. aarch64 has 81 registers: 31
//!    GPRs, 1 stack pointer register, 1 zero register, 32 vector registers, and
//!    16 predicate registers with SVE. riscv64 has 96 registers: 32 GPRs, 32
//!    floats, and 32 vectors. Other ISAs have similar counts. New ISA
//!    extensions keep adding more registers of an existing kind (e.g. x86-64's
//!    APX) or introducing new kinds of registers (e.g. aarch64's SVE and its
//!    predicate registers). We want capacity to support not just the registers
//!    of today's ISAs, but also whatever new ISA extensions come in the future
//!    as well.
//!
//! 4. Overlapping register classes.
//!
//!    This allows modeling instructions that can only access half of the
//!    register bank (e.g. riscv64's compact instructions or an x86-64 vector
//!    instruction that doesn't have an EVEX form) -- such instructions simply
//!    reference operands of a register class that names a subset of the
//!    registers named in the "full" register class.
//!
//! 5. Preferred registers.
//!
//!    Some registers may be cheaper to use than others (for example,
//!    caller-saved registers don't require this function to save and restore
//!    their clobbered values in its prologue and epilogue) and their allocation
//!    should be preferred over callee-save registers in low-register-pressure
//!    scenarios.
//!
//! 6. Subregister aliasing.
//!
//!    This is the ability to explicitly model the `al` portion of `rax`, for
//!    example, and, honestly, it is the least important item on the list. It is
//!    nice for, e.g., arm32 and how the `s0` and `s1` halves can be named and
//!    written independently from their `d0` whole, but it makes testing
//!    register interference more expensive. A subtle benefit of modeling
//!    subregister units is that some calling conventions only require a portion
//!    of a register be saved by callers (aapcs64 only saves the bottom 64 bits
//!    of `v8`-`v15`; win64 saves `xmm6`-`xmm15` but not `ymm6`-`ymm15`) so if
//!    we model subregister units, we can save just the portion of the register
//!    that is necessary around calls, rather than the full register, resulting
//!    in smaller frame sizes.
//!
//! Note that our model doesn't necessarily need to *explicitly name* all of the
//! above concepts, but they should either be expressible in or emergent from
//! the model.
//!
//! So what is our model and how does it support those features?
//!
//! The user defines the target machine in terms of the following types:
//!
//! * `RegUnit`: The smallest accessible portion of a register. Different
//!   `RegUnit`s cannot overlap with each other. A `RegUnit` is atomic and
//!   cannot be broken down any further.
//!
//! * `Reg`: A register. This is a contiguous range of `RegUnit`s. `Reg`s are
//!   associated with a register bank, and while two different `Reg`s may name
//!   overlapping `RegUnit`s, if they do then they may not be associated with
//!   the same register bank.
//!
//! * `RegGroup`: A set of registers that an instruction can name all together
//!   as a single operand. There are no constraints on the registers within a
//!   group: they may or may not be contiguous, or even-aligned, etc... If the
//!   target machine has such requirements, the user should defined the groups
//!   accordingly.
//!
//! * `RegClass`: A set of either `Reg`s or `RegGroup`s whose members an operand
//!   can be assigned to. `RegClass`es can overlap with other `RegClass`es or be
//!   sub- or superclasses. A `RegClass` has an associated spill cost.
//!
//! * `RegBank`: A set of disjoint `Reg`s of the same kind. These registers can
//!   always be moved between. Two `Reg`s within the same `RegBank` may not have
//!   overlapping `RegUnit`s.
//!
//!   Modeling riscv64, we could define a register bank for each of GPRs, float
//!   registers, and vector registers. Modeling x86-64, we can choose between a
//!   coarse-grained model or fine-grained model depending on our use case: a
//!   coarse-grained model would be a register bank for all the GPRs and another
//!   register bank for all the `xmm`/`ymm`/`zmm` registers; a fine-grained
//!   model could express `al` separately from `ax`, `eax`, and `rax` and `xmm0`
//!   separately from `ymm0` and `zmm0` by defining the following register
//!   banks:
//!
//!   * the byte-sized portions of the GPRs (`al`, `bl`, etc...),
//!   * the 16-bit portions of the GPRs (`ax`, `bx`, etc...),
//!   * the 32-bit portions of the GPRs (`eax`, `ebx`, etc...),
//!   * the 64-bit portions of the GPRs (`rax`, `rbx`, etc...),
//!   * the 128-bit `xmm` portions of the SSE registers,
//!   * the 256-bit `ymm` portions of the SSE registers, and
//!   * the 512-bit `zmm` portions of the SSE registers.
//!
//!   We would just need to take care to make sure that the registers between
//!   each bank are defined with overlapping register units to model their
//!   interference correctly.
//!
//! How does this model satisfy our desiderata? We explicitly support naming
//! disjoint register banks (1). Registers that cover an empty range of units
//! are implicitly considered non-allocatable (2). We have a large register
//! index space (3) of up to 512 registers. We support register classes with
//! arbitrary overlap, subclassing, and superclassing (4) and defining up to 64
//! different register classes. Register preferrence (5) is determined
//! implicitly via the order of registers named within a register
//! class. Subregister aliasing (6) is supported via the distinction between
//! registers and register units.

use crate::{
    Entity, EntityRepr, Error, Result,
    entity::{FixedEntitySet, PrimaryMap, words_for},
};
use alloc::{boxed::Box, collections::BTreeMap, vec, vec::Vec};
use core::ops::Range;

define_fixed_size_entities! {
    /// The smallest accessible portion of a register.
    ///
    /// Two different `RegUnit`s can never overlap.
    ///
    /// Note that we do not *allocate* `RegUnit`s (we allocate [`Reg`]s for
    /// instruction operands, not `RegUnit`s). `RegUnit`s only exist to express
    /// subregister aliasing and interference.
    ///
    /// When an ISA doesn't have "overlapping" registers or different names for
    /// the high- or low-halves of a register (or if you don't need to model
    /// these ISA intricacies) then `RegUnit`s can be one-to-one with `Reg`s,
    /// and you needn't think about them further.
    ///
    /// Otherwise, when you do with to support and model subregister aliasing, a
    /// `RegUnit` is the smallest portion of a register that can be accessed by
    /// an instruction, and then registers are built by declaring which
    /// `RegUnit`s they cover. This allows you to express conflict between
    /// registers, or portions of registers.
    ///
    /// On arm32, for example, the `i`th `d` register is made up of the `i*2`th
    /// `s` register as its low half and the `i*2+1`th `s` register as its high
    /// half:
    ///
    /// ```ignore
    /// +-------------------------+
    /// |    d0   |    d1   | ... |
    /// | s0 | s1 | s2 | s3 | ... |
    /// +-------------------------+
    /// ```
    ///
    /// You can model this by creating a `RegUnit` for each `s` register, and
    /// then defining the `s` registers one-to-one with these units and each `d`
    /// register as covering the `[i*2, i*2+1]` units.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegUnit: u16 = "unit";


    /// A group of registers that may be named as a whole by a single
    /// instruction operand.
    ///
    /// All registers in a group must be associated with the same [`RegBank`].
    ///
    /// This is useful for ISAs that have instructions that operate on, e.g.,
    /// the `i`th and `i+1`th register at the same time, while only explicitly
    /// naming the first. s390x has many instructions that name even or odd
    /// pairs of registers: 0 and 2, 1 and 3, 4 and 6, 5 and 7, etc...
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegGroup: u16 = "group";


    /// A set of [`Reg`]s or [`RegGroup`]s that are candidate operands to some
    /// instruction.
    ///
    /// An instruction operand declares its valid candidates by naming a
    /// `RegClass`.
    ///
    /// The members of a `RegClass` are named in most-to-least preferred order.
    ///
    /// A `RegClass` may not be empty.
    ///
    /// All registers in a `RegClass` must be associated with the same
    /// [`RegBank`].
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegClass: u8 = "rc";


    /// A set of registers of the same "kind".
    ///
    /// It must always be possible to move values between allocatable [`Reg`]s
    /// within the same `RegBank` with a singe move instruction.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RegBank: u8 = "bank";
}

define_entities! {
    /// A register.
    ///
    /// Instruction operands get allocated to [`Reg`]s (or, sometimes,
    /// [`RegGroup`]s).
    ///
    /// A `Reg` covers a contiguous range of [`RegUnit`]s, which allows
    /// expressing subregister interference and aliasing (e.g. `eax` and `rax`
    /// on x86-64).
    ///
    /// A `Reg` has an associated [`RegBank`]. All registers associated with the
    /// same [`RegBank`] must have disjoint [`RegUnit`]s.
    ///
    /// A `Reg` may appear in any number of [`RegClass`]es.
    ///
    /// A `Reg` is "non-allocatable" when it covers an empty range of
    /// [`RegUnit`]s, which means that the register allocator does not "own" the
    /// register and will never draw upon it when it needs a register, but that
    /// it may still be named as an operand by instructions. This is useful for
    /// special instructions that read or write, for example, the stack pointer
    /// or link registers. Only allocatable registers may be used as temporaries
    /// for stack-to-stack moves.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Reg = "r";
}

impl RegUnit {
    /// The maximum number of `RegUnit`s supported.
    pub const MAX: usize = 512;
}

impl Reg {
    /// The maximum number of `Reg`s supported.
    pub const MAX: usize = 512;
}

impl<E> Reg<E>
where
    E: EntityRepr,
{
    /// The range of units that this register covers.
    #[inline]
    pub(crate) fn units(self, machine: &Machine) -> Range<RegUnit> {
        machine.registers[self.with_repr32()].units.clone()
    }

    /// This register's associated register bank.
    #[inline]
    pub(crate) fn bank(self, machine: &Machine) -> RegBank {
        machine.registers[self.with_repr32()].bank
    }

    /// Does this register cover any units, and so may be allocated?
    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub(crate) fn is_allocatable(self, machine: &Machine) -> bool {
        let units = &machine.registers[self.with_repr32()].units;
        units.start != units.end
    }

    /// Does this register cover no units, and so may never be allocated?
    #[inline]
    #[expect(dead_code, reason = "will probably need it")]
    pub(crate) fn is_non_allocatable(self, machine: &Machine) -> bool {
        !self.is_allocatable(machine)
    }
}

impl RegGroup {
    /// The maximum number of `RegGroup`s supported.
    pub const MAX: usize = 512;

    /// The maximum number of `Reg`s in a single `RegGroup`.
    pub const MAX_SIZE: usize = 8;

    /// The members of this group, in order.
    #[inline]
    pub(crate) fn members(self, machine: &Machine) -> &[Reg] {
        &machine.groups[self].members
    }

    /// The same registers as `self.members(machine)`, as a set for fast
    /// membership and interference testing rather than in order.
    #[inline]
    pub(crate) fn member_set(self, machine: &Machine) -> &RegSet {
        &machine.groups[self].member_set
    }

    /// This register group's associated register bank.
    #[inline]
    #[expect(
        dead_code,
        reason = "the sibling of Reg::bank and RegClass::bank, kept for symmetry"
    )]
    pub(crate) fn bank(self, machine: &Machine) -> RegBank {
        machine.groups[self].bank
    }
}

impl RegClass {
    /// The maximum number of `RegClass`es that the user may define.
    pub const MAX: usize = 64;

    /// The maximum number of `RegClass`es supported, including the ones that
    /// `MachineBuilder::finish` derives.
    pub(crate) const MAX_INCLUDING_DERIVED: usize = 2 * Self::MAX;

    /// The cost of spilling this register class.
    #[inline]
    pub(crate) fn spill_cost(self, machine: &Machine) -> f32 {
        machine.classes[self].spill_cost
    }

    /// The members of this register class.
    #[inline]
    pub(crate) fn members(self, machine: &Machine) -> &RegClassMembers {
        &machine.classes[self].members
    }

    /// Does this class contain exactly one register (or one register group)?
    #[inline]
    pub(crate) fn is_singleton(self, machine: &Machine) -> bool {
        match self.members(machine) {
            RegClassMembers::Regs(regs) => regs.len() == 1,
            RegClassMembers::Groups(groups) => groups.len() == 1,
        }
    }

    /// How many registers a value of this register-group class occupies, or
    /// `None` when it is a single-register class.
    #[inline]
    pub(crate) fn group_size(self, machine: &Machine) -> Option<usize> {
        match self.members(machine) {
            RegClassMembers::Groups(groups) => Some(groups[0].members(machine).len()),
            RegClassMembers::Regs(_) => None,
        }
    }

    /// The same set of registers inside `self.members(machine)`, but as a
    /// `RegSet` for fast interference testing, rather than in
    /// allocation-preferrence order.
    #[inline]
    pub(crate) fn member_set(self, machine: &Machine) -> &RegSet {
        &machine.classes[self].member_set
    }

    /// This register class's associated register bank.
    #[inline]
    pub(crate) fn bank(self, machine: &Machine) -> RegBank {
        machine.classes[self].bank
    }

    /// The class whose members are the registers in both `self` and `other`, or
    /// `None` when they have no members in common.
    ///
    /// This is what makes [`crate::input::OperandConstraint`]'s merge total: the
    /// intersection of two classes is always either empty or itself a class.
    #[inline]
    pub(crate) fn intersect(self, machine: &Machine, other: RegClass) -> Option<RegClass> {
        let n = machine.classes.len();
        debug_assert!(self.index() < n);
        debug_assert!(other.index() < n);
        machine.class_intersections[self.index() * n + other.index()]
    }
}

impl RegBank {
    /// The maximum number of `RegBank`s supported.
    pub const MAX: usize = 64;

    /// The number of distinct register sizes that a machine can have.
    ///
    /// A size is a power of two that fits in a `u16`, so there are sixteen of
    /// them: `1 << 0` through `1 << 15`.
    pub(crate) const NUM_SIZES: usize = 16;

    /// The base-two logarithm of the byte size of this bank's registers.
    ///
    /// This is always less than `RegBank::NUM_SIZES`.
    #[inline]
    pub(crate) fn log2_size(self, machine: &Machine) -> u8 {
        let log2_size = machine.banks[self].log2_size;
        debug_assert!(usize::from(log2_size) < Self::NUM_SIZES);
        log2_size
    }

    /// The set of registers that belong to this register bank.
    #[inline]
    #[allow(dead_code, reason = "will probably need it")]
    pub(crate) fn registers(self, machine: &Machine) -> &RegSet {
        &machine.banks[self].registers
    }

    /// The subset of `self.registers(machine)` that may be borrowed as a
    /// scratch register to split a stack-to-stack move in two or break a
    /// parallel-move cycle.
    #[inline]
    pub(crate) fn stack_to_stack_move_regs(self, machine: &Machine) -> RegSet {
        let bank = &machine.banks[self];
        debug_assert!(bank.non_allocatable.is_subset_of(&bank.registers));
        bank.registers.difference(&bank.non_allocatable)
    }
}

/// A set of `Reg`s.
pub type RegSet = FixedEntitySet<Reg, { words_for(Reg::MAX) }>;

#[derive(Clone, Debug)]
pub(crate) struct RegDef {
    /// The range of units that this register covers.
    pub units: Range<RegUnit>,

    /// This register's associated register bank.
    pub bank: RegBank,
}

#[derive(Clone, Debug)]
pub(crate) struct RegGroupDef {
    /// The members of this group, in order.
    ///
    /// The order is part of the definition: an instruction that names a group
    /// typically encodes only its first register, and a target whose groups are
    /// irregular pairs -- s390x's `FP128` pairing of (0,2), (1,3), (4,6), ... --
    /// needs to say which register comes first.
    pub members: Box<[Reg]>,

    /// The same registers as `self.members`, as a set for fast membership and
    /// interference testing rather than in order.
    pub member_set: RegSet,

    /// This register group's associated register bank.
    pub bank: RegBank,
}

#[derive(Clone, Debug)]
pub(crate) struct RegClassDef {
    /// The cost of spilling this register class.
    pub spill_cost: f32,

    /// The members of this register class.
    pub members: RegClassMembers,

    /// The same set of registers inside `self.members`, but as a `RegSet` for
    /// fast interference testing, rather than in allocation-preferrence order.
    pub member_set: RegSet,

    /// This register class's associated register bank.
    pub bank: RegBank,
}

#[derive(Clone, Debug)]
pub(crate) enum RegClassMembers {
    /// A register class made up of the given registers, ordered by preferrence.
    Regs(Box<[Reg]>),
    /// A register class made up of the given register groups, ordered by
    /// preferrence.
    Groups(Box<[RegGroup]>),
}

#[derive(Clone, Debug)]
pub(crate) struct RegBankDef {
    /// The set of registers that belong to this register bank.
    registers: RegSet,

    /// The subset of `self.registers` that are "non-allocatable".
    non_allocatable: RegSet,

    /// The base-two logarithm of the byte size of this bank's registers.
    log2_size: u8,
}

/// Trait for checking interference (conflict) between two things.
#[allow(dead_code, reason = "will probably need it")]
pub(crate) trait Interfere<Rhs = Self> {
    /// Does `lhs` interfere with `rhs`?
    fn interfere(machine: &Machine, lhs: Self, rhs: Rhs) -> bool;
}

impl<T> Interfere for &T
where
    T: Clone + Interfere,
{
    #[inline]
    fn interfere(machine: &Machine, lhs: &T, rhs: &T) -> bool {
        Interfere::interfere(machine, lhs.clone(), rhs.clone())
    }
}

impl Interfere for Reg {
    #[inline]
    fn interfere(machine: &Machine, lhs: Self, rhs: Self) -> bool {
        return if lhs == rhs {
            true
        } else {
            slow(machine, lhs, rhs)
        };

        fn slow(machine: &Machine, lhs: Reg, rhs: Reg) -> bool {
            let lhs = &machine.registers[lhs];
            let rhs = &machine.registers[rhs];
            if lhs.bank == rhs.bank {
                // Registers in the same bank are disjoint.
                debug_assert!(!Interfere::interfere(machine, &lhs.units, &rhs.units));
                false
            } else {
                // Otherwise, they interfere if their units interfere.
                Interfere::interfere(machine, &lhs.units, &rhs.units)
            }
        }
    }
}

impl Interfere for Range<RegUnit> {
    #[inline]
    fn interfere(_machine: &Machine, lhs: Self, rhs: Self) -> bool {
        lhs.start < rhs.end && rhs.start < lhs.end
    }
}

/// The model of the machine whose registers we are allocating.
///
/// Construct a `Machine` via a [`MachineBuilder`].
#[derive(Clone, Debug)]
pub struct Machine {
    registers: PrimaryMap<Reg, RegDef>,
    groups: PrimaryMap<RegGroup, RegGroupDef>,
    classes: PrimaryMap<RegClass, RegClassDef>,
    #[allow(dead_code, reason = "will probably need it")]
    banks: PrimaryMap<RegBank, RegBankDef>,

    /// For each pair of register classes, the class whose members are the
    /// registers (or groups) in both of them, if there is one.
    ///
    /// Indexed by `a.index() * self.classes.len() + b.index()`, and symmetric.
    /// `None` means the two classes have no members in common, and so no
    /// operand can satisfy constraints naming both.
    ///
    /// Derived by `MachineBuilder::finish`.
    class_intersections: Box<[Option<RegClass>]>,

    /// How many of `self.classes` the user defined.
    ///
    /// The rest are the intersections that [`MachineBuilder::finish`] derived,
    /// appended after them so that the [`RegClass`]es handed out while building
    /// keep their indices.
    num_user_classes: usize,
}

impl Machine {
    /// How many registers this machine has.
    #[inline]
    pub fn num_registers(&self) -> usize {
        self.registers.len()
    }

    /// How many register classes the user defined, as opposed to the ones
    /// derived from them.
    #[inline]
    pub(crate) fn num_user_classes(&self) -> usize {
        self.num_user_classes
    }
}

/// Builds a `Machine`.
///
/// Declare the register banks first, then define the registers, groups and
/// classes that populate them, then call [`MachineBuilder::finish`], which
/// checks the whole description and hands back the [`Machine`].
///
/// # Example: Building a Simple x86-64 `Machine`
///
/// This is a simple x86-64 `Machine` that models all general-purpose registers
/// as one bank and all float/SSE registers as another bank. It does not bother
/// to model subregisters (e.g. there is no `al`, `ax`, or `eax`, only `rax`).
///
/// Because nothing here overlaps, the register units are one-to-one with the
/// registers, and you can ignore the distinction.
///
/// ```
/// use regicide::{Entity, MachineBuilder, RegUnit};
///
/// let mut builder = MachineBuilder::new();
///
/// // A bank is a set of registers that a value can always be moved between, so
/// // the GPRs are one bank and the SSE registers are another.
/// //
/// // Both banks hold eight-byte registers because this model has no
/// // subregisters and treats an `xmm` as the eight bytes a IEEE754 value
/// // actually occupies.
/// let gpr = builder.declare_reg_bank(8)?;
/// let sse = builder.declare_reg_bank(8)?;
///
/// let unit = |i: usize| RegUnit::try_new(i).unwrap();
///
/// // The sixteen GPRs, in x86-64's own numbering: rax, rcx, rdx, rbx, rsp, rbp,
/// // rsi, rdi, r8, ..., r15.
/// let mut gprs = Vec::new();
/// for i in 0..16 {
///     gprs.push(if i == 4 {
///         // rsp is the stack pointer. Instructions may name it, but the
///         // allocator must never assign a value to it, so it is defined as
///         // non-allocatable and left out of every class below.
///         builder.define_non_allocatable_reg(gpr)?
///     } else {
///         builder.define_reg(gpr, unit(i)..unit(i + 1))?
///     });
/// }
///
/// // The sixteen XMM registers, whose units continue where the GPRs left off,
/// // because two registers may only share units across banks when they really
/// // do overlap in the hardware.
/// let mut xmms = Vec::new();
/// for i in 16..32 {
///     xmms.push(builder.define_reg(sse, unit(i)..unit(i + 1))?);
/// }
///
/// // A class is both the set of registers an operand may be assigned to and the
/// // order to prefer them in, so the caller-saved registers come first: using
/// // one costs nothing, while using a callee-saved register makes this function
/// // save and restore it.
/// let caller_saved = [0, 1, 2, 6, 7, 8, 9, 10, 11];
/// let callee_saved = [3, 5, 12, 13, 14, 15];
/// let gpr_class = builder.define_reg_class(
///     gpr,
///     1.0,
///     caller_saved.into_iter().chain(callee_saved).map(|i| gprs[i]),
/// )?;
///
/// // xmm0-xmm7 are caller-saved under the SysV ABI; the rest are too, but a
/// // Windows target would order these differently.
/// let sse_class = builder.define_reg_class(sse, 1.0, xmms.iter().copied())?;
///
/// // Finally, build the machine!
/// let machine = builder.finish()?;
/// # Ok::<(), regicide::Error>(())
/// ```
///
/// # Example: Building an Arm32 `Machine`
///
/// This `Machine` models Arm32 and differentiates between `s` registers `d`
/// registers, which overlap with each other: the `i`th `d` register is made up
/// of the `2*i`th `s` register as its low half and the `2*i+1`th `s` register
/// as its high half.
///
/// This demonstrates [`RegUnit`]'s purpose. The `s` and `d` registers go in
/// separate banks -- registers within one bank must be disjoint -- and naming
/// the same units from both banks is what makes `s0` and `s1` interfere with
/// `d0`.
///
/// ```
/// use regicide::{Entity, MachineBuilder, RegUnit};
///
/// let mut builder = MachineBuilder::new();
///
/// // An `s` register is four bytes wide and a `d` register is eight.
/// let s_bank = builder.declare_reg_bank(4)?;
/// let d_bank = builder.declare_reg_bank(8)?;
///
/// let unit = |i: usize| RegUnit::try_new(i).unwrap();
///
/// // The 32 single-precision registers are the finest-grained view of this
/// // register file, so they are one-to-one with the units.
/// let mut s = Vec::new();
/// for i in 0..32 {
///     s.push(builder.define_reg(s_bank, unit(i)..unit(i + 1))?);
/// }
///
/// // Each double-precision register covers the two units that its two halves
/// // cover: `d[i]` is `s[2 * i]` and `s[2 * i + 1]` together.
/// let mut d = Vec::new();
/// for i in 0..16 {
///     d.push(builder.define_reg(d_bank, unit(2 * i)..unit(2 * i + 2))?);
/// }
///
/// let s_class = builder.define_reg_class(s_bank, 1.0, s.iter().copied())?;
/// let d_class = builder.define_reg_class(d_bank, 1.0, d.iter().copied())?;
///
/// let mut pairs = Vec::new();
/// for i in 0..8 {
///     pairs.push(builder.define_reg_group(d_bank, [d[2 * i], d[2 * i + 1]])?);
/// }
///
/// // Instructions like `vld2` operate on several `d` registers at once while
/// // encoding only the first, which is what a register group expresses.
/// let pair_class = builder.define_reg_group_class(d_bank, 2.0, pairs.iter().copied())?;
///
/// let machine = builder.finish()?;
/// # Ok::<(), regicide::Error>(())
/// ```
pub struct MachineBuilder {
    registers: PrimaryMap<Reg, RegDef>,
    groups: PrimaryMap<RegGroup, RegGroupDef>,
    classes: PrimaryMap<RegClass, RegClassDef>,
    banks: PrimaryMap<RegBank, RegBankDef>,
}

impl Default for MachineBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl MachineBuilder {
    /// Create a new, empty machine description.
    pub const fn new() -> Self {
        Self {
            registers: PrimaryMap::new(),
            groups: PrimaryMap::new(),
            classes: PrimaryMap::new(),
            banks: PrimaryMap::new(),
        }
    }

    /// Declare a register bank whose registers are `size` bytes wide.
    ///
    /// Registers within one bank must cover disjoint register units; registers in
    /// different banks may overlap. A bank is the set of registers that a value
    /// can be moved between.
    ///
    /// The size is the byte size of a spilled value of this bank occupies on
    /// the stack. It must be a power of two.
    ///
    /// # Errors
    ///
    /// Returns an error if `byte_size` is not a power of two, or if the machine
    /// already has [`RegBank::MAX`] banks.
    pub fn declare_reg_bank(&mut self, byte_size: u16) -> Result<RegBank> {
        if !byte_size.is_power_of_two() {
            return Err(Error::BadRegBankSize { size: byte_size });
        }
        if self.banks.len() < RegBank::MAX {
            Ok(self.banks.push_unwrap(RegBankDef {
                registers: RegSet::new(),
                non_allocatable: RegSet::new(),
                log2_size: u8::try_from(byte_size.trailing_zeros()).unwrap(),
            }))
        } else {
            Err(Error::MachineCapacityExceeded {
                what: "register banks",
                max: RegBank::MAX,
            })
        }
    }

    /// Define a register that the allocator owns.
    ///
    /// Registers within the same bank must be disjoint. A register that covers no
    /// units at all is one that exists only to be named, never allocated, and so
    /// must belong to no class.
    ///
    /// The order registers are given in a [`RegClass`] is what expresses
    /// preference between them; defining one here says only that it exists. To
    /// define a register that the allocator may not draw upon freely, use
    /// [`MachineBuilder::define_non_allocatable_reg`] instead.
    pub fn define_reg(&mut self, bank: RegBank, units: Range<RegUnit>) -> Result<Reg> {
        self.define_reg_impl(bank, units, Allocatable::Yes)
    }

    /// Define a register that the allocator does not own.
    ///
    /// The allocator will not draw upon this register when it needs one, and in
    /// particular will never stage a stack-to-stack move through it -- but
    /// instructions may still name it as an operand, and it still interferes
    /// with the registers it overlaps. This is how to model the stack pointer, a
    /// link register, a hardware zero register, or a flags register.
    ///
    /// A non-allocatable register may still be a member of a [`RegClass`]. A
    /// class holding one such register is how an operand says it must go in that
    /// particular register and nowhere else, which is the point of naming these
    /// registers at all.
    ///
    /// Give it whatever units it really covers, so that it interferes correctly;
    /// an empty range suits a register with nothing to conflict with.
    pub fn define_non_allocatable_reg(&mut self, bank: RegBank) -> Result<Reg> {
        self.define_reg_impl(
            bank,
            Entity::MAX_REPRESENTABLE..Entity::MAX_REPRESENTABLE,
            Allocatable::No,
        )
    }

    fn define_reg_impl(
        &mut self,
        bank: RegBank,
        units: Range<RegUnit>,
        allocatable: Allocatable,
    ) -> Result<Reg> {
        self.check_bank(bank)?;

        // Check the capacity before pushing, because the register goes straight
        // into a fixed-capacity `RegSet` below.
        check_capacity(self.registers.len() + 1, Reg::MAX, "registers")?;

        let reg = self.registers.next_key_unwrap();
        match allocatable {
            Allocatable::Yes => {
                if units.start > units.end || units.end.index() > RegUnit::MAX {
                    return Err(Error::BadRegUnitRange { reg });
                }
            }
            Allocatable::No => {
                assert_eq!(units.start, Entity::MAX_REPRESENTABLE);
                assert_eq!(units.start, units.end);
            }
        }

        let reg2 = self.registers.push_unwrap(RegDef { units, bank });
        assert_eq!(reg, reg2);
        self.banks[bank].registers.insert(reg);
        if allocatable == Allocatable::No {
            self.banks[bank].non_allocatable.insert(reg);
        }
        Ok(reg)
    }

    /// Define a register group in this machine.
    ///
    /// All registers in the group must belong to the same bank, and the order
    /// they are given in is the group's order.
    pub fn define_reg_group(
        &mut self,
        bank: RegBank,
        registers: impl IntoIterator<Item = Reg>,
    ) -> Result<RegGroup> {
        self.check_bank(bank)?;
        check_capacity(self.groups.len() + 1, RegGroup::MAX, "register groups")?;

        let members: Box<[Reg]> = registers.into_iter().collect();
        let group = self.groups.next_key_unwrap();

        if !(2..=RegGroup::MAX_SIZE).contains(&members.len()) {
            return Err(Error::BadRegGroupSize {
                group,
                len: members.len(),
            });
        }

        let mut member_set = RegSet::new();
        for &reg in &members {
            self.check_reg_in_bank(reg, bank)?;
            if !member_set.insert(reg) {
                return Err(Error::DuplicateRegGroupMember { group, reg });
            }
        }

        Ok(self.groups.push_unwrap(RegGroupDef {
            members,
            member_set,
            bank,
        }))
    }

    /// Define a register class of individual registers in this machine.
    ///
    /// All `registers` must belong to `bank`.
    ///
    /// `registers` is both the class's membership and its preferred allocation
    /// order, so put the registers that are cheaper to use (e.g. have smaller
    /// encoding) first.
    ///
    /// A class of exactly one register is how an operand demands that register
    /// and no other.
    ///
    /// `registers` must be non-empty.
    pub fn define_reg_class(
        &mut self,
        bank: RegBank,
        spill_cost: f32,
        registers: impl IntoIterator<Item = Reg>,
    ) -> Result<RegClass> {
        assert!(spill_cost.is_sign_positive());

        let class = self.begin_class(bank)?;
        let members: Box<[Reg]> = registers.into_iter().collect();
        if members.is_empty() {
            return Err(Error::EmptyRegClass { class });
        }

        let mut member_set = RegSet::new();
        for &reg in &members {
            self.check_class_member(class, reg, bank)?;
            if !member_set.insert(reg) {
                return Err(Error::DuplicateRegClassMember { class, reg });
            }
        }

        Ok(self.classes.push_unwrap(RegClassDef {
            spill_cost,
            members: RegClassMembers::Regs(members),
            member_set,
            bank,
        }))
    }

    /// Define a register class of register groups in this machine.
    ///
    /// All of the groups must belong to `bank` and have the same size.
    ///
    /// As with [`MachineBuilder::define_reg_class`], the order given is the
    /// preferred allocation order.
    ///
    /// `groups` must be non-empty.
    pub fn define_reg_group_class(
        &mut self,
        bank: RegBank,
        spill_cost: f32,
        groups: impl IntoIterator<Item = RegGroup>,
    ) -> Result<RegClass> {
        assert!(spill_cost.is_sign_positive());

        let class = self.begin_class(bank)?;
        let members: Box<[RegGroup]> = groups.into_iter().collect();
        if members.is_empty() {
            return Err(Error::EmptyRegClass { class });
        }

        let mut member_set = RegSet::new();
        let mut size = None;
        for &group in &members {
            if group.index() >= self.groups.len() || self.groups[group].bank != bank {
                return Err(Error::RegGroupInWrongBank {
                    group,
                    expected: bank,
                });
            }

            let len = self.groups[group].members.len();
            match size {
                None => size = Some(len),
                Some(size) if size != len => return Err(Error::MixedRegGroupSizes { class }),
                Some(_) => {}
            }

            // Groups within a class may overlap, so a register appearing in
            // several of them is fine.
            for i in 0..len {
                let reg = self.groups[group].members[i];
                self.check_class_member(class, reg, bank)?;
                member_set.insert(reg);
            }
        }

        Ok(self.classes.push_unwrap(RegClassDef {
            spill_cost,
            members: RegClassMembers::Groups(members),
            member_set,
            bank,
        }))
    }

    /// Validate the machine description and produce the [`Machine`].
    pub fn finish(mut self) -> Result<Machine> {
        check_capacity(self.banks.len(), RegBank::MAX, "register banks")?;

        for (bank, def) in self.banks.iter() {
            // The interference property: within a bank, distinct registers never
            // share a unit, which is what lets `Interfere for Reg` answer with an
            // integer comparison instead of a unit test.
            //
            // Sorting by where each register's units start means an overlap, if
            // there is one, is between neighbours.
            let mut regs: Vec<Reg> = def
                .registers
                .iter()
                .filter(|&r| self.registers[r].units.start < self.registers[r].units.end)
                .collect();
            regs.sort_unstable_by_key(|&r| self.registers[r].units.start);
            for pair in regs.windows(2) {
                let (a, b) = (pair[0], pair[1]);
                if self.registers[b].units.start < self.registers[a].units.end {
                    return Err(Error::OverlappingRegsInBank { bank, a, b });
                }
            }

            // Two spill slots can need a move between them -- a block parameter
            // in one and its incoming value in another -- and hardware cannot do
            // that directly, so every bank needs somewhere to stage it.
            debug_assert!(def.non_allocatable.is_subset_of(&def.registers));
            if def.registers.difference(&def.non_allocatable).is_empty() {
                return Err(Error::NoStackToStackRegs { bank });
            }
        }

        let num_user_classes = self.classes.len();
        let class_intersections = self.define_class_intersections()?;

        let Self {
            registers,
            groups,
            classes,
            banks,
        } = self;
        Ok(Machine {
            registers,
            groups,
            classes,
            banks,
            class_intersections,
            num_user_classes,
        })
    }

    /// Derive the register classes that name the intersections of the classes
    /// the user defined, and tabulate them.
    ///
    /// Merging two operands' constraints (an operand that must be in class `a`
    /// and, because of a reuse or a shared value, must also be in class `b`)
    /// needs a class naming the registers in both. Therefore, the class list
    /// has to be closed under intersection, and closed transitively:
    /// intersecting two derived classes must land on a class too, or merging
    /// could fail on constraints the user never wrote down. That is what the
    /// worklist below gives, by intersecting each class, derived ones included,
    /// against everything before it.
    ///
    /// This is affordable because, in practice, typical machines derive almost
    /// nothing.
    fn define_class_intersections(&mut self) -> Result<Box<[Option<RegClass>]>> {
        let mut dedupe = BTreeMap::new();
        for i in 0..self.classes.len() {
            let class = RegClass::try_new(i).unwrap();
            dedupe
                .entry(self.class_key(&self.classes[class]))
                .or_insert(class);
        }

        // Close the class list under intersection.
        let mut next = 0;
        while next < self.classes.len() {
            for a in 0..next {
                let a = RegClass::try_new(a).unwrap();
                let b = RegClass::try_new(next).unwrap();
                let Some(def) = self.intersect_class_defs(a, b) else {
                    continue;
                };
                let key = self.class_key(&def);
                if dedupe.contains_key(&key) {
                    continue;
                }
                check_capacity(
                    self.classes.len() + 1,
                    RegClass::MAX_INCLUDING_DERIVED,
                    "register classes, including the intersections derived from them",
                )?;
                let class = self.classes.push_unwrap(def);
                dedupe.insert(key, class);
            }
            next += 1;
        }

        // Now tabulate.
        let n = self.classes.len();
        let mut table = vec![None; n * n];
        for a in 0..n {
            // A class is its own intersection with itself.
            table[a * n + a] = Some(RegClass::try_new(a).unwrap());

            for b in 0..a {
                let (x, y) = (RegClass::try_new(b).unwrap(), RegClass::try_new(a).unwrap());
                let Some(def) = self.intersect_class_defs(x, y) else {
                    continue;
                };
                let class = dedupe.get(&self.class_key(&def)).copied();
                debug_assert!(
                    class.is_some(),
                    "the register class list is closed under intersection",
                );
                table[a * n + b] = class;
                table[b * n + a] = class;
            }
        }

        Ok(table.into_boxed_slice())
    }

    /// The definition of the class holding exactly the members that both `a` and
    /// `b` have, or `None` when they have none in common.
    ///
    /// `a`'s preference order is kept, which is what makes this symmetric up to
    /// preference, and so makes merging two constraints commutative.
    fn intersect_class_defs(&self, a: RegClass, b: RegClass) -> Option<RegClassDef> {
        let (x, y) = (&self.classes[a], &self.classes[b]);

        // Registers in different banks are always disjoint.
        if x.bank != y.bank {
            return None;
        }

        let members = match (&x.members, &y.members) {
            (RegClassMembers::Regs(xs), RegClassMembers::Regs(_)) => {
                let regs: Box<[Reg]> = xs
                    .iter()
                    .copied()
                    .filter(|&reg| y.member_set.contains(reg))
                    .collect();
                if regs.is_empty() {
                    return None;
                }
                RegClassMembers::Regs(regs)
            }

            (RegClassMembers::Groups(xs), RegClassMembers::Groups(ys)) => {
                // A class of groups has a single group size, so classes of
                // differently-sized groups fall out of this as empty.
                let groups: Box<[RegGroup]> = xs
                    .iter()
                    .copied()
                    .filter(|group| ys.contains(group))
                    .collect();
                if groups.is_empty() {
                    return None;
                }
                RegClassMembers::Groups(groups)
            }

            // An operand names either one register or one whole group, never
            // both, so these classes have no common members even when they cover
            // the same registers.
            (RegClassMembers::Regs(_), RegClassMembers::Groups(_))
            | (RegClassMembers::Groups(_), RegClassMembers::Regs(_)) => return None,
        };

        Some(RegClassDef {
            // The intersection is a subset of both, so it is at least as
            // expensive to spill as either of them.
            spill_cost: x.spill_cost.max(y.spill_cost),
            member_set: self.member_set(&members),
            members,
            bank: x.bank,
        })
    }

    /// The registers that `members` covers, as a set.
    fn member_set(&self, members: &RegClassMembers) -> RegSet {
        let mut set = RegSet::new();
        match members {
            RegClassMembers::Regs(regs) => {
                for &reg in regs {
                    set.insert(reg);
                }
            }
            RegClassMembers::Groups(groups) => {
                for &group in groups {
                    for &reg in &self.groups[group].members {
                        set.insert(reg);
                    }
                }
            }
        }
        set
    }

    /// The key that identifies `class` in the hash-consing table.
    fn class_key(&self, class: &RegClassDef) -> ClassKey {
        match &class.members {
            // Keyed on the member set, as the user's classes are: which
            // registers an operand of this class may go in is what makes two
            // classes the same class, and the order among them is only a
            // preference.
            RegClassMembers::Regs(_) => ClassKey::Regs(class.member_set.clone()),

            // A class of groups needs more than that: a `RegSet` does not say
            // how the registers are grouped, so two different group lists can
            // cover the very same registers. Sorted, since the order is a
            // preference here too.
            RegClassMembers::Groups(groups) => {
                let mut groups = groups.clone();
                groups.sort_unstable();
                ClassKey::Groups(groups)
            }
        }
    }

    fn check_bank(&self, bank: RegBank) -> Result<()> {
        if bank.index() < self.banks.len() {
            Ok(())
        } else {
            Err(Error::UnknownRegBank { bank })
        }
    }

    fn check_reg_in_bank(&self, reg: Reg, bank: RegBank) -> Result<()> {
        if reg.index() < self.registers.len() && self.registers[reg].bank == bank {
            Ok(())
        } else {
            Err(Error::RegInWrongBank {
                reg,
                expected: bank,
            })
        }
    }

    /// Check a register that is about to become a member of `class`.
    fn check_class_member(&self, _class: RegClass, reg: Reg, bank: RegBank) -> Result<()> {
        self.check_reg_in_bank(reg, bank)?;
        Ok(())
    }

    /// Check what both kinds of register class need checked, and name the class
    /// that is about to be defined, so that a validation failure can blame it.
    fn begin_class(&mut self, bank: RegBank) -> Result<RegClass> {
        self.check_bank(bank)?;
        check_capacity(self.classes.len() + 1, RegClass::MAX, "register classes")?;
        Ok(self.classes.next_key_unwrap())
    }
}

/// The identity of a register class, for deduplicating the classes that
/// `MachineBuilder::define_class_intersections` derives.
///
/// Two classes with the same key are interchangeable, so only the first of them
/// needs to exist.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ClassKey {
    /// A class of individual registers, identified by the set.
    Regs(RegSet),

    /// A class of register groups, identified by sorted members.
    Groups(Box<[RegGroup]>),
}

/// Check that having `len` of something is within its limit.
fn check_capacity(len: usize, max: usize, what: &'static str) -> Result<()> {
    if len <= max {
        Ok(())
    } else {
        Err(Error::MachineCapacityExceeded { what, max })
    }
}

/// Whether the allocator owns a register being defined.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Allocatable {
    Yes,
    No,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn machine_is_send_sync() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}
        assert_send::<Machine>();
        assert_sync::<Machine>();
    }

    fn unit(i: usize) -> RegUnit {
        RegUnit::try_new(i).unwrap()
    }

    /// A bank's register size must be a power of two, because it is stored as a
    /// base-two logarithm and used to index the spill slot pools.
    #[test]
    fn reg_bank_sizes_must_be_powers_of_two() {
        let mut builder = MachineBuilder::new();
        for size in [1, 2, 4, 8, 16, 1 << 15] {
            let bank = builder.declare_reg_bank(size).unwrap();
            let machine_size = 1u16 << builder.banks[bank].log2_size;
            assert_eq!(machine_size, size, "{size} did not round-trip");
        }
        for size in [0, 3, 6, 7, 100, u16::MAX] {
            assert!(
                matches!(
                    builder.declare_reg_bank(size),
                    Err(Error::BadRegBankSize { size: bad }) if bad == size,
                ),
                "{size} is not a power of two, so it should be rejected",
            );
        }
    }

    /// Build a machine exercising every shape the builder can express, and check
    /// what it derived.
    #[test]
    fn build_a_machine() {
        // Two banks: four one-unit registers plus a unit-less non-allocatable one
        // that exists only to be named, and two two-unit registers whose units
        // overlap the first bank's, which is legal precisely because they are in
        // another bank.
        let mut builder = MachineBuilder::new();
        let gpr = builder.declare_reg_bank(8).unwrap();
        let vector = builder.declare_reg_bank(8).unwrap();

        let r: Vec<Reg> = (0..4)
            .map(|i| builder.define_reg(gpr, unit(i)..unit(i + 1)).unwrap())
            .collect();
        let sp = builder.define_non_allocatable_reg(gpr).unwrap();
        let v: Vec<Reg> = (0..2)
            .map(|i| {
                builder
                    .define_reg(vector, unit(2 * i)..unit(2 * i + 2))
                    .unwrap()
            })
            .collect();

        // `r[3]` is allocatable but left out of every class, so no value is ever
        // assigned to it.
        let class = builder
            .define_reg_class(gpr, 1.0, [r[0], r[1], r[2]])
            .unwrap();

        let group = builder.define_reg_group(vector, [v[0], v[1]]).unwrap();
        let group_class = builder
            .define_reg_group_class(vector, 2.0, [group])
            .unwrap();

        let machine = builder.finish().expect("this machine is well formed");

        // Membership in a class is preference, not ownership: `r[3]` is in no
        // class, but the allocator still owns it, so it may stage a
        // stack-to-stack move.
        assert!(gpr.registers(&machine).contains(r[3]));
        assert!(!class.member_set(&machine).contains(r[3]));
        assert!(gpr.stack_to_stack_move_regs(&machine).contains(r[3]));
        assert!(gpr.stack_to_stack_move_regs(&machine).contains(r[0]));

        // A non-allocatable register belongs to its bank -- it still interferes
        // with what it overlaps -- but must not reach the scratch pool: staging a
        // move through the stack pointer would clobber it.
        assert!(gpr.registers(&machine).contains(sp));
        assert!(!class.member_set(&machine).contains(sp));
        assert!(!gpr.stack_to_stack_move_regs(&machine).contains(sp));

        // A group's order is part of its definition.
        assert_eq!(group.members(&machine), &[v[0], v[1]]);
        assert!(matches!(
            *group_class.members(&machine),
            RegClassMembers::Groups(_)
        ));

        // The interference property: identity within a bank, unit overlap across
        // banks.
        assert!(Reg::interfere(&machine, r[0], r[0]));
        assert!(!Reg::interfere(&machine, r[0], r[1]));
        assert!(Reg::interfere(&machine, r[0], v[0]));
        assert!(!Reg::interfere(&machine, r[2], v[0]));
    }

    #[test]
    fn reject_overlapping_regs_in_one_bank() {
        let mut builder = MachineBuilder::new();
        let bank = builder.declare_reg_bank(8).unwrap();
        let a = builder.define_reg(bank, unit(0)..unit(2)).unwrap();
        let b = builder.define_reg(bank, unit(1)..unit(3)).unwrap();
        builder.define_reg_class(bank, 1.0, [a, b]).unwrap();
        assert!(matches!(
            builder.finish().unwrap_err(),
            Error::OverlappingRegsInBank { .. }
        ));
    }

    #[test]
    fn reject_bank_with_no_scratch_reg() {
        // A bank whose every register is non-allocatable has nowhere to stage a
        // stack-to-stack move.
        let mut builder = MachineBuilder::new();
        let bank = builder.declare_reg_bank(8).unwrap();
        builder.define_non_allocatable_reg(bank).unwrap();
        assert!(matches!(
            builder.finish().unwrap_err(),
            Error::NoStackToStackRegs { .. }
        ));
    }

    /// A class whose only member is a non-allocatable register is how an operand
    /// demands that one register, so it must be buildable -- while the register
    /// stays out of the scratch pool, which is what non-allocatable means.
    #[test]
    fn allow_non_allocatable_reg_in_a_class() {
        let mut builder = MachineBuilder::new();
        let bank = builder.declare_reg_bank(8).unwrap();
        let r0 = builder.define_reg(bank, unit(0)..unit(1)).unwrap();
        let flags = builder.define_non_allocatable_reg(bank).unwrap();

        let general = builder.define_reg_class(bank, 1.0, [r0]).unwrap();
        let fixed = builder.define_reg_class(bank, 1.0, [flags]).unwrap();

        // And by way of a group, which is the other route into a class.
        let group = builder.define_reg_group(bank, [r0, flags]).unwrap();
        let group_class = builder.define_reg_group_class(bank, 2.0, [group]).unwrap();

        let machine = builder.finish().expect("this machine is well formed");

        assert!(fixed.member_set(&machine).contains(flags));
        assert!(group_class.member_set(&machine).contains(flags));
        assert!(!general.member_set(&machine).contains(flags));

        // Being in a class does not put it back in the scratch pool.
        assert!(!bank.stack_to_stack_move_regs(&machine).contains(flags));
        assert!(bank.stack_to_stack_move_regs(&machine).contains(r0));
    }

    #[test]
    fn reject_bad_groups_and_banks() {
        let mut builder = MachineBuilder::new();
        let x = builder.declare_reg_bank(8).unwrap();
        let y = builder.declare_reg_bank(8).unwrap();
        let x0 = builder.define_reg(x, unit(0)..unit(1)).unwrap();
        let x1 = builder.define_reg(x, unit(1)..unit(2)).unwrap();
        let y0 = builder.define_reg(y, unit(0)..unit(1)).unwrap();

        assert!(matches!(
            builder.define_reg_group(x, [x0, y0]).unwrap_err(),
            Error::RegInWrongBank { .. }
        ));
        assert!(matches!(
            builder.define_reg_group(x, [x0]).unwrap_err(),
            Error::BadRegGroupSize { .. }
        ));
        assert!(matches!(
            builder.define_reg_group(x, [x0, x0]).unwrap_err(),
            Error::DuplicateRegGroupMember { .. }
        ));
        assert!(matches!(
            builder.define_reg_class(x, 1.0, [x0, x1, x0]).unwrap_err(),
            Error::DuplicateRegClassMember { .. }
        ));
        assert!(matches!(
            builder
                .define_reg(RegBank::try_new(9).unwrap(), unit(0)..unit(1))
                .unwrap_err(),
            Error::UnknownRegBank { .. }
        ));
        assert!(matches!(
            builder.define_reg(x, unit(2)..unit(1)).unwrap_err(),
            Error::BadRegUnitRange { .. }
        ));
    }

    #[test]
    fn reject_empty_classes() {
        let mut builder = MachineBuilder::new();
        let bank = builder.declare_reg_bank(8).unwrap();
        assert!(matches!(
            builder.define_reg_class(bank, 1.0, []).unwrap_err(),
            Error::EmptyRegClass { .. }
        ));
        assert!(matches!(
            builder.define_reg_group_class(bank, 1.0, []).unwrap_err(),
            Error::EmptyRegClass { .. }
        ));
    }

    /// The classes a machine derives, and the table it answers intersection
    /// queries from.
    #[test]
    fn derive_class_intersections() {
        let mut builder = MachineBuilder::new();
        let gpr = builder.declare_reg_bank(8).unwrap();
        let vector = builder.declare_reg_bank(8).unwrap();

        let r: Vec<Reg> = (0..4)
            .map(|i| builder.define_reg(gpr, unit(i)..unit(i + 1)).unwrap())
            .collect();
        let v: Vec<Reg> = (0..2)
            .map(|i| builder.define_reg(vector, unit(i)..unit(i + 1)).unwrap())
            .collect();

        // `nested` is a subset of `all`, so that pair derives nothing. `low` and
        // `high` cross -- each holds a register the other lacks -- and so do
        // `nested` and `high`, so those two pairs each derive a class.
        //
        // `all` and `low` cover the same registers in different orders, so their
        // intersection dedups onto `low` and derives nothing: the cons table is
        // keyed on the member *set*, which is exactly what makes the table
        // symmetric.
        let all = builder
            .define_reg_class(gpr, 1.0, [r[0], r[1], r[2], r[3]])
            .unwrap();
        let nested = builder.define_reg_class(gpr, 2.0, [r[0], r[1]]).unwrap();
        let low = builder
            .define_reg_class(gpr, 3.0, [r[2], r[1], r[0]])
            .unwrap();
        let high = builder
            .define_reg_class(gpr, 4.0, [r[1], r[2], r[3]])
            .unwrap();

        // In another bank, and reached by way of groups, so it intersects with
        // nothing above it.
        let group = builder.define_reg_group(vector, [v[0], v[1]]).unwrap();
        let groups = builder
            .define_reg_group_class(vector, 5.0, [group])
            .unwrap();

        let num_user_classes = 5;
        let machine = builder.finish().expect("this machine is well formed");
        assert_eq!(machine.num_user_classes(), num_user_classes);

        // Two classes were derived, in the order the worklist reached them:
        // `nested` and `high` intersect in `{r[1]}`, and `low` and `high` in
        // `{r[1], r[2]}`.
        assert_eq!(machine.classes.len(), num_user_classes + 2);
        let singleton = nested.intersect(&machine, high).unwrap();
        let crossing = low.intersect(&machine, high).unwrap();
        assert_eq!(singleton.index(), num_user_classes);
        assert_eq!(crossing.index(), num_user_classes + 1);

        // And their own intersection is the smaller of them, which is the
        // closure holding transitively: a derived class intersected with another
        // derived class still lands on a class.
        assert_eq!(singleton.intersect(&machine, crossing), Some(singleton));

        // `low` is the lower-indexed of the pair, so its preference order is the
        // one that survives -- which is what makes the table symmetric, and so
        // `OperandConstraint::merge` commutative.
        let RegClassMembers::Regs(members) = crossing.members(&machine) else {
            panic!("intersecting two classes of registers gives a class of registers");
        };
        assert_eq!(&**members, &[r[2], r[1]]);
        assert_eq!(high.intersect(&machine, low), Some(crossing));

        // Spilling a subset is at least as expensive as spilling either class it
        // came from.
        assert_eq!(crossing.spill_cost(&machine), high.spill_cost(&machine),);

        // A subset relationship derives nothing: the intersection is the subset.
        assert_eq!(all.intersect(&machine, nested), Some(nested));
        assert_eq!(nested.intersect(&machine, low), Some(nested));

        // Every class is its own intersection with itself, including the derived
        // one, and including classes that would otherwise dedup onto each other.
        for i in 0..machine.classes.len() {
            let class = RegClass::try_new(i).unwrap();
            assert_eq!(class.intersect(&machine, class), Some(class));
        }

        // Different banks, and registers against groups, have nothing in common.
        assert_eq!(all.intersect(&machine, groups), None);
        assert_eq!(groups.intersect(&machine, all), None);

        // The closure property, which is what `merge` totality rests on:
        // intersecting any two classes -- derived ones included -- either lands
        // on a class or on nothing, never on a set that needs a new class.
        for a in 0..machine.classes.len() {
            let a = RegClass::try_new(a).unwrap();
            for b in 0..machine.classes.len() {
                let b = RegClass::try_new(b).unwrap();
                assert_eq!(
                    a.intersect(&machine, b),
                    b.intersect(&machine, a),
                    "the intersection table is symmetric",
                );
                if let Some(ab) = a.intersect(&machine, b) {
                    // And it is a fixed point: intersecting the result with
                    // either parent gives the result back.
                    assert_eq!(ab.intersect(&machine, a), Some(ab));
                    assert_eq!(ab.intersect(&machine, b), Some(ab));
                }
            }
        }
    }

    /// Closing the class list under intersection can blow up, and when it does
    /// `finish` must say so rather than derive its way past `RegClass::MAX`.
    ///
    /// Eight classes of the form "every register except `r_i`" have all 256
    /// "every register except `S`" subsets in their closure.
    #[test]
    fn reject_too_many_derived_classes() {
        let mut builder = MachineBuilder::new();
        let bank = builder.declare_reg_bank(8).unwrap();
        let r: Vec<Reg> = (0..16)
            .map(|i| builder.define_reg(bank, unit(i)..unit(i + 1)).unwrap())
            .collect();

        for i in 0..8 {
            let members: Vec<Reg> = r
                .iter()
                .copied()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, reg)| reg)
                .collect();
            builder.define_reg_class(bank, 1.0, members).unwrap();
        }

        assert!(matches!(
            builder.finish().unwrap_err(),
            Error::MachineCapacityExceeded { .. }
        ));
    }

    #[test]
    fn reject_mixed_group_sizes_in_a_class() {
        let mut builder = MachineBuilder::new();
        let bank = builder.declare_reg_bank(8).unwrap();
        let r: Vec<Reg> = (0..5)
            .map(|i| builder.define_reg(bank, unit(i)..unit(i + 1)).unwrap())
            .collect();
        let pair = builder.define_reg_group(bank, [r[0], r[1]]).unwrap();
        let triple = builder.define_reg_group(bank, [r[2], r[3], r[4]]).unwrap();
        assert!(matches!(
            builder
                .define_reg_group_class(bank, 1.0, [pair, triple])
                .unwrap_err(),
            Error::MixedRegGroupSizes { .. }
        ));
    }
}
