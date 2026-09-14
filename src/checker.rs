//! Checking the results of register allocation.
//!
//! Register allocation is a rewrite of a program's storage, and this checks
//! that the rewrite preserved what the program meant:
//!
//! * every operand's allocation holds the operand's value where the operand is
//!   read and satisfies its constraint,
//!
//! * no two definitions of one instruction write to the same location, and
//!
//! * the inserted moves and rematerializations carry values from where the
//!   allocation left them to where the next instruction needs them.
//!
//! The checker never looks at the allocator's own bookkeeping or intermediary
//! data structures: it reads operands from the input, allocations and edits
//! from the allocator's output, and works out for itself what values each
//! machine location holds.
//!
//! This is a form of *translation validation*: we are proving equivalence
//! between the machine-level and abstract value-level versions of the program
//! for all inputs that could be given to the program. (We are not proving that
//! `regicide` itself is correct for all program inputs; just proving
//! correctness of _this_ program's register allocation.)
//!
//! The checker is implemented with abstract interpretation. For each program
//! point (i.e. this is flow sensitive), we track the set of values that are
//! definitely (i.e. this is a "must" analysis) in each machine location (each
//! register or spill slot). These sets of values are a meet semilattice where
//! the empty set is bottom and the meet function is set intersection.
//!
//! First we run `Checker::analyze`, which runs the abstract interpretation to a
//! fixpoint. The machine state is initialized according to what
//! `Output::block_param_allocs` reports for the entry block's parameter -- the
//! caller places its arguments here, and, by initializing the machine state
//! accordingly, we are assuming callers correctly do that, but we do check that
//! back edges to the entry block preserve correct placement. The fixpoint loop
//! terminates because the value set for a machine location at a particular
//! program point can only shrink.
//!
//! After the fixpoint completes, we run `Checker::find_errors`, which inspects
//! the fixpoint results at each program point for equivalence violations:
//! ensuring that each machine-level instruction operand contains exactly the
//! value that the input-level instruction operand named, whether the
//! machine-level location matches the operand's constraint, etc...

use crate::{
    entity::{Block, Inst, SecondaryMap, Val},
    input::{
        DefUse, Input, InputBlock, InputFunction, InputInst, InputValue, Operand, OperandConstraint,
    },
    machine::{Interfere, Machine, Reg, RegBank, RegClass, RegClassMembers},
    output::{
        Allocation, CriticalEdgeEdit, EdgeEdit, Edit, InstOrEdit, Move, Output, RegAllocation,
        Remat, ScalarAllocation, StackAllocation,
    },
    spill_slot_allocation::{SpillSlot, SpillSlotSize},
};
use alloc::{
    collections::{BTreeMap, BTreeSet},
    vec::Vec,
};
use core::fmt;

/// Check that `output` is a correct register allocation of `input`.
///
/// On failure, reports the set of violations found.
pub fn check(
    input: &Input<'_, impl InputFunction>,
    output: &Output<'_>,
) -> Result<(), CheckerErrors> {
    let mut checker = Checker::new(input, output);
    checker.analyze();
    checker.find_errors();
    checker.finish()
}

/// Everything that [`check`] found wrong with an allocation.
#[derive(Clone)]
pub struct CheckerErrors {
    errors: Vec<CheckerError>,
}

impl CheckerErrors {
    /// The problems found, in the order the checker walked the program.
    pub fn errors(&self) -> &[CheckerError] {
        &self.errors
    }
}

impl fmt::Debug for CheckerErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "the allocation has {} problem(s):", self.errors.len())?;
        for error in &self.errors {
            write!(f, "\n  * {error:?}")?;
        }
        Ok(())
    }
}

impl fmt::Display for CheckerErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl core::error::Error for CheckerErrors {}

/// One thing wrong with an allocation.
#[derive(Clone, PartialEq, Eq)]
pub enum CheckerError {
    /// An instruction has a different number of allocations than it has
    /// operands.
    WrongAllocCount {
        /// The [`Inst`] whose allocations were counted.
        inst: Inst,
        /// The number of operands the instruction has.
        expected: usize,
        /// The number of allocations it was given.
        actual: usize,
    },

    /// A critical-edge edit appears among the edits atop a block.
    ///
    /// The edits before a block's first instruction are the ones its single
    /// incoming edge delivers. A critical-edge edit goes on an edge the client
    /// still has to split, which is never one of those, and the block's own
    /// outgoing edges come at the end of its stream rather than the start.
    CriticalEdgeEditAtBlockEntry {
        /// The [`Block`] whose entry edits it sits in.
        block: Block,
        /// The misplaced edit.
        edit: CriticalEdgeEdit,
    },

    /// An instruction or point edit appears after a block's critical-edge
    /// edits, which are the last thing its stream holds: everything the block
    /// itself runs has already happened by then.
    ItemAfterCriticalEdgeEdits {
        /// The [`Block`] whose stream it sits in.
        block: Block,
        /// The misplaced instruction or edit.
        item: InstOrEdit,
    },

    /// The results put something in a spill slot they never allocated, so
    /// there is no size to hold it to and no stack for it to live on.
    NoSuchSpillSlot {
        /// The [`SpillSlot`] the results name but do not allocate.
        slot: SpillSlot,
    },

    /// A block has a different number of parameter allocations than it has
    /// parameters.
    ///
    /// The two are walked in lock-step, so without this the shorter of them
    /// silently decides how many parameters are checked at all.
    WrongBlockParamAllocCount {
        /// The [`Block`] whose parameter allocations were counted.
        block: Block,
        /// The number of parameters the block has.
        expected: usize,
        /// The number of allocations it was given.
        actual: usize,
    },

    /// An operand's allocation is made of a different number of locations than
    /// its value occupies registers.
    WrongScalarCount {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
        /// How many registers the operand's value occupies.
        expected: usize,
        /// How many locations its allocation is made of.
        actual: usize,
    },

    /// A group-resident value is allocated a single location, or a
    /// single-register value a group.
    GroupMismatch {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
    },

    /// An operand is allocated to a spill slot that is not the size of one of
    /// its value's registers.
    WrongSpillSlotSize {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
        /// The offending [`SpillSlot`].
        slot: SpillSlot,
        /// The size of a register of the value's bank.
        expected: SpillSlotSize,
        /// The slot's actual size.
        actual: SpillSlotSize,
    },

    /// An allocation is a register, or a register group, that is not a member
    /// of the register class it has to be in.
    ///
    /// For an operand that class is the one the instruction asked for; for a
    /// block parameter it is the parameter's own, a contract nothing could
    /// meet.
    NotInRegClass {
        /// Where the allocation came from.
        site: Site,
        /// The [`RegClass`] the allocation had to be a member of.
        class: RegClass,
        /// The [`RegAllocation`] it is instead.
        alloc: RegAllocation,
    },

    /// A definition lands in a non-allocatable register.
    ///
    /// A non-allocatable register covers no register units, so nothing the
    /// allocator does can keep a value that lives in one from being trampled;
    /// the register is only in a class at all so that an operand can pin a
    /// *read* to it. Defining a value there claims a home the allocator does
    /// not own.
    DefInNonAllocatableReg {
        /// Where the allocation came from.
        site: Site,
        /// The non-allocatable [`Reg`] the definition landed in.
        reg: Reg,
    },

    /// An operand that must be in a register is on the stack.
    NotAReg {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
    },

    /// An operand that must be on the stack is in a register.
    NotOnStack {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
    },

    /// An operand with a [`OperandConstraint::Reuse`] constraint is not in the
    /// same location as the operand it names.
    ReuseMismatch {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the reusing operand within the instruction.
        operand: usize,
        /// Where the reusing operand went.
        alloc: Allocation,
        /// The index of the operand it reuses.
        target: usize,
        /// Where the reused operand went, if the instruction has such an
        /// operand at all.
        target_alloc: Option<Allocation>,
    },

    /// An operand reads a location that does not hold the value it names.
    WrongValue {
        /// The [`Inst`] the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
        /// The [`Val`] the operand names.
        val: Val,
        /// Which of the value's registers this is: `0` for a value that lives
        /// in a single register, and the index of the group member otherwise.
        index: usize,
        /// The location that should have held it.
        loc: ScalarAllocation,
        /// The values that location holds instead, which is empty when the
        /// checker cannot tell what is there.
        actual: Vec<Val>,
    },

    /// Two of one instruction's definitions write the same location, so
    /// whichever of them runs first is destroyed by the other.
    ConflictingDef {
        /// The [`Inst`] whose definitions collide.
        inst: Inst,
        /// The index of the later of the two operands.
        operand: usize,
        /// The index of the earlier of the two operands.
        other: usize,
        /// The location they both write.
        loc: ScalarAllocation,
    },

    /// A definition writes a location that another operand of the same
    /// instruction reads at the same point, destroying the value being read.
    DefClobbersUse {
        /// The [`Inst`] whose operands collide.
        inst: Inst,
        /// The index of the defining operand.
        operand: usize,
        /// The index of the reading operand it destroys.
        other: usize,
        /// The location they share.
        loc: ScalarAllocation,
    },

    /// A value the input does not say may be rematerialized was
    /// rematerialized anyway.
    NotRematerializable {
        /// The [`Block`] whose edits rematerialize it.
        block: Block,
        /// The [`Val`] that was rematerialized.
        val: Val,
    },

    /// A value that occupies more than one register was rematerialized, which
    /// a [`Remat`] has no way to express: it names one destination register.
    RematOfRegGroup {
        /// The [`Block`] whose edits rematerialize it.
        block: Block,
        /// The [`Val`] that was rematerialized.
        val: Val,
    },

    /// A value that is not computed from nothing was rematerialized.
    ///
    /// A [`Remat`] recomputes its value on its own, wherever it is placed, so
    /// the only values it can express are the ones whose defining instruction
    /// reads nothing. Rematerializing anything else recomputes it from whatever
    /// happens to be lying around at the destination instead of from what the
    /// definition read.
    RematOfDerivedValue {
        /// The [`Block`] whose edits rematerialize it.
        block: Block,
        /// The [`Val`] that was rematerialized.
        val: Val,
        /// The [`Inst`] that defines it, or `None` when it is a block
        /// parameter.
        def: Option<Inst>,
    },

    /// A block parameter is not in the location the results say it arrives in.
    MisplacedBlockParam {
        /// The [`Block`] whose parameter it is.
        block: Block,
        /// The parameter [`Val`].
        param: Val,
        /// Where the results say it arrives.
        alloc: Allocation,
    },

    /// Two of a block's parameters are reported as arriving in the same
    /// location, so whichever is put there first is destroyed by the other.
    ConflictingBlockParams {
        /// The [`Block`] whose parameters collide.
        block: Block,
        /// The later of the two parameters.
        param: Val,
        /// The earlier of the two parameters.
        other: Val,
        /// The location they both arrive in.
        loc: ScalarAllocation,
    },

    /// A block parameter's reported arrival is made of a different number of
    /// locations than the parameter occupies registers.
    BlockParamWrongScalarCount {
        /// The [`Block`] whose parameter it is.
        block: Block,
        /// The parameter [`Val`].
        param: Val,
        /// How many registers the parameter occupies.
        expected: usize,
        /// How many locations its reported arrival is made of.
        actual: usize,
    },

    /// A group-resident block parameter is reported arriving in a single
    /// location, or a single-register one in a group.
    BlockParamGroupMismatch {
        /// The [`Block`] whose parameter it is.
        block: Block,
        /// The parameter [`Val`].
        param: Val,
        /// Where the results say it arrives.
        alloc: Allocation,
    },

    /// A block parameter is reported arriving in a spill slot that is not the
    /// size of one of its registers.
    BlockParamWrongSpillSlotSize {
        /// The [`Block`] whose parameter it is.
        block: Block,
        /// The parameter [`Val`].
        param: Val,
        /// The offending [`SpillSlot`].
        slot: SpillSlot,
        /// The size of a register of the parameter's bank.
        expected: SpillSlotSize,
        /// The slot's actual size.
        actual: SpillSlotSize,
    },

    /// A move puts a value in a register of a bank the value cannot live in.
    ///
    /// Banks rather than classes: coalesced values sharing a location need not
    /// agree on a class, but values sharing a register do share its bank.
    BadMoveBank {
        /// The [`Block`] whose edits contain the move.
        block: Block,
        /// The [`Val`] the move carries.
        val: Val,
        /// The [`RegBank`] the value lives in.
        expected: RegBank,
        /// The [`RegBank`] of the register it was moved to.
        actual: RegBank,
    },

    /// A move puts a value in a spill slot that is not the size of one of the
    /// value's registers.
    WrongMoveSlotSize {
        /// The [`Block`] whose edits contain the move.
        block: Block,
        /// The [`Val`] the move carries.
        val: Val,
        /// The offending [`SpillSlot`].
        slot: SpillSlot,
        /// The size of a register of the value's bank.
        expected: SpillSlotSize,
        /// The slot's actual size.
        actual: SpillSlotSize,
    },

    /// A move's two registers are of different banks, so neither end can
    /// hold what the other does. Unlike [`CheckerError::BadMoveBank`] this is
    /// a property of the move alone, caught even when the checker does not
    /// know what the move carries.
    MismatchedMoveBanks {
        /// The [`Block`] whose edits contain the move.
        block: Block,
        /// The offending move.
        mov: Move,
        /// The bank of the register the move reads.
        from: RegBank,
        /// The bank of the register the move writes.
        to: RegBank,
    },

    /// A move's spill slot is not the size of the register at the move's
    /// other end. Unlike [`CheckerError::WrongMoveSlotSize`] this is a
    /// property of the move alone, caught even when the checker does not know
    /// what the move carries.
    MismatchedMoveSlotSize {
        /// The [`Block`] whose edits contain the move.
        block: Block,
        /// The offending move.
        mov: Move,
        /// The slot at one end of it.
        slot: SpillSlot,
        /// The size of the register at the other end.
        expected: SpillSlotSize,
        /// The slot's actual size.
        actual: SpillSlotSize,
    },

    /// A rematerialization puts its value in a register that is not a member
    /// of the value's own register class.
    RematNotInRegClass {
        /// The [`Block`] whose edits rematerialize it.
        block: Block,
        /// The [`Val`] that was rematerialized.
        val: Val,
        /// The [`RegClass`] the destination had to be a member of.
        class: RegClass,
        /// The [`Reg`] it was rematerialized into instead.
        reg: Reg,
    },

    /// A move puts something in a register the machine never lets the
    /// allocator hand out, and that whatever it put there is not allowed to
    /// live in.
    ///
    /// Unlike a definition (see [`CheckerError::DefInNonAllocatableReg`]), a
    /// move into a non-allocatable register is perfectly ordinary: it is how a
    /// value reaches an operand pinned to `sp`, or to the flags. What makes one
    /// wrong is the register not being somewhere that value was ever allowed or
    /// the move's source holding nothing the checker can name, in which case
    /// nothing about the destination can be justified at all.
    MoveIntoNonAllocatableReg {
        /// The [`Block`] whose edits contain the move.
        block: Block,
        /// The [`Val`] the move put there, if the checker knows of one.
        val: Option<Val>,
        /// The non-allocatable [`Reg`] the move wrote.
        reg: Reg,
    },

    /// A move or rematerialization sits after a block's terminator, where the
    /// machine would never run it.
    ///
    /// Running an edit there is the same as running it on the block's outgoing
    /// edge, but only when the terminator is the whole of that edge: the block
    /// must have a single successor, and the terminator must have no operands
    /// of its own for the edit to disturb. Anything else belongs on the edge,
    /// as a [`CriticalEdgeEdit`].
    EditAfterTerminator {
        /// The [`Block`] whose edits contain it.
        block: Block,
        /// The terminator it comes after.
        terminator: Inst,
        /// The offending edit.
        edit: EdgeEdit,
    },

    /// A [`CriticalEdgeEdit`] names an edge that its block does not have, or
    /// names a target that is not where that edge goes.
    BadCriticalEdgeSuccessor {
        /// The [`Block`] the edge leaves.
        block: Block,
        /// The index of the successor edge the edit claims to be on.
        succ: usize,
        /// The [`Block`] the edit claims that edge goes to.
        target: Block,
    },
}

impl fmt::Debug for CheckerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongAllocCount {
                inst,
                expected,
                actual,
            } => write!(
                f,
                "{inst:?} has {expected} operand(s) but was given {actual} allocation(s)"
            ),
            Self::CriticalEdgeEditAtBlockEntry { block, edit } => write!(
                f,
                "{edit:?} sits among the edits atop {block:?}, which are the ones its incoming \
                 edge delivers"
            ),
            Self::ItemAfterCriticalEdgeEdits { block, item } => write!(
                f,
                "{item:?} comes after {block:?}'s critical-edge edits, which are the last thing \
                 its stream may hold"
            ),
            Self::NoSuchSpillSlot { slot } => {
                write!(f, "the results use {slot:?}, which they do not allocate")
            }
            Self::WrongBlockParamAllocCount {
                block,
                expected,
                actual,
            } => write!(
                f,
                "{block:?} has {expected} parameter(s) but was given {actual} allocation(s)"
            ),
            Self::WrongScalarCount {
                inst,
                operand,
                expected,
                actual,
            } => write!(
                f,
                "operand {operand} of {inst:?} occupies {expected} register(s) but its \
                 allocation is made of {actual} location(s)"
            ),
            Self::GroupMismatch { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} is allocated to a group but its value does not \
                 live in one, or the other way around"
            ),
            Self::WrongSpillSlotSize {
                inst,
                operand,
                slot,
                expected,
                actual,
            } => write!(
                f,
                "operand {operand} of {inst:?} is allocated to {slot:?}, which is {} byte(s) \
                 rather than the {} byte(s) one of its registers needs",
                actual.size(),
                expected.size(),
            ),
            Self::NotInRegClass { site, class, alloc } => {
                // Which of the two shapes it is goes without saying: the name
                // of a group does not read like the name of a register.
                let alloc: &dyn fmt::Debug = match alloc {
                    RegAllocation::Reg(reg) => reg,
                    RegAllocation::RegGroup(group) => group,
                };
                write!(
                    f,
                    "{site:?} is allocated to {alloc:?}, which is not in {class:?}"
                )
            }
            Self::MoveIntoNonAllocatableReg {
                block,
                val: Some(val),
                reg,
            } => write!(
                f,
                "a move in {block:?} puts {val:?} in {reg:?}, which is not allocatable and not in \
                 {val:?}'s own register class"
            ),
            Self::MoveIntoNonAllocatableReg {
                block,
                val: None,
                reg,
            } => write!(
                f,
                "a move in {block:?} puts an unknown value in {reg:?}, which is not allocatable"
            ),
            Self::DefInNonAllocatableReg { site, reg } => write!(
                f,
                "{site:?} is defined in {reg:?}, which is not allocatable"
            ),
            Self::NotAReg { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} must be in a register but is on the stack"
            ),
            Self::NotOnStack { inst, operand } => write!(
                f,
                "operand {operand} of {inst:?} must be on the stack but is in a register"
            ),
            Self::ReuseMismatch {
                inst,
                operand,
                alloc,
                target,
                target_alloc,
            } => write!(
                f,
                "operand {operand} of {inst:?} is in {alloc:?} but reuses operand {target}, \
                 which is in {target_alloc:?}"
            ),
            Self::WrongValue {
                inst,
                operand,
                val,
                index,
                loc,
                actual,
            } => {
                write!(
                    f,
                    "operand {operand} of {inst:?} reads register {index} of {val:?} from \
                     {loc:?}, which holds "
                )?;
                if actual.is_empty() {
                    write!(f, "nothing the checker knows of")
                } else {
                    write!(f, "{actual:?}")
                }
            }
            Self::ConflictingDef {
                inst,
                operand,
                other,
                loc,
            } => write!(
                f,
                "operands {other} and {operand} of {inst:?} both define {loc:?}"
            ),
            Self::DefClobbersUse {
                inst,
                operand,
                other,
                loc,
            } => write!(
                f,
                "operand {operand} of {inst:?} defines {loc:?}, which operand {other} reads at \
                 the same point"
            ),
            Self::NotRematerializable { block, val } => write!(
                f,
                "{block:?} rematerializes {val:?}, which the input does not give a \
                 rematerialization cost"
            ),
            Self::RematOfRegGroup { block, val } => write!(
                f,
                "{block:?} rematerializes {val:?}, which occupies more than one register"
            ),
            Self::RematOfDerivedValue {
                block,
                val,
                def: Some(def),
            } => write!(
                f,
                "{block:?} rematerializes {val:?}, which {def:?} computes from values it reads"
            ),
            Self::RematOfDerivedValue {
                block,
                val,
                def: None,
            } => write!(
                f,
                "{block:?} rematerializes {val:?}, which is a block parameter and so no \
                 instruction computes"
            ),
            Self::MisplacedBlockParam {
                block,
                param,
                alloc,
            } => write!(
                f,
                "{param:?} arrives in {block:?} in {alloc:?} according to the results, but is \
                 not there"
            ),
            Self::ConflictingBlockParams {
                block,
                param,
                other,
                loc,
            } => write!(
                f,
                "parameters {other:?} and {param:?} of {block:?} both arrive in {loc:?}"
            ),
            Self::BlockParamWrongScalarCount {
                block,
                param,
                expected,
                actual,
            } => write!(
                f,
                "{param:?} of {block:?} occupies {expected} register(s) but is reported \
                 arriving in {actual} location(s)"
            ),
            Self::BlockParamGroupMismatch {
                block,
                param,
                alloc,
            } => write!(
                f,
                "{param:?} of {block:?} is reported arriving in {alloc:?}, which is a register \
                 group exactly when {param:?} is not"
            ),
            Self::BlockParamWrongSpillSlotSize {
                block,
                param,
                slot,
                expected,
                actual,
            } => write!(
                f,
                "{param:?} of {block:?} is reported arriving in {slot:?}, which is {} byte(s) \
                 rather than the {} byte(s) one of its registers needs",
                actual.size(),
                expected.size(),
            ),
            Self::BadMoveBank {
                block,
                val,
                expected,
                actual,
            } => write!(
                f,
                "a move in {block:?} puts {val:?} in a register of {actual:?}, but {val:?} \
                 lives in {expected:?}"
            ),
            Self::WrongMoveSlotSize {
                block,
                val,
                slot,
                expected,
                actual,
            } => write!(
                f,
                "a move in {block:?} puts {val:?} in {slot:?}, which is {} byte(s) rather than \
                 the {} byte(s) one of its registers needs",
                actual.size(),
                expected.size(),
            ),
            Self::MismatchedMoveBanks {
                block,
                mov,
                from,
                to,
            } => write!(
                f,
                "{mov:?} in {block:?} reads {from:?} and writes {to:?}, which are different banks"
            ),
            Self::MismatchedMoveSlotSize {
                block,
                mov,
                slot,
                expected,
                actual,
            } => write!(
                f,
                "{mov:?} in {block:?} names {slot:?}, which is {} byte(s) rather than the {} \
                 byte(s) the register at its other end needs",
                actual.size(),
                expected.size(),
            ),
            Self::RematNotInRegClass {
                block,
                val,
                class,
                reg,
            } => write!(
                f,
                "{block:?} rematerializes {val:?} into {reg:?}, which is not in {class:?}"
            ),
            Self::EditAfterTerminator {
                block,
                terminator,
                edit,
            } => write!(
                f,
                "{edit:?} in {block:?} comes after {terminator:?}, which is not an edge this \
                 edit may be placed on"
            ),
            Self::BadCriticalEdgeSuccessor {
                block,
                succ,
                target,
            } => write!(
                f,
                "an edit on {block:?}'s successor edge {succ} says that edge goes to {target:?}, \
                 which is not where it goes"
            ),
        }
    }
}

impl fmt::Display for CheckerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl core::error::Error for CheckerError {}

/// Where an allocation being checked for legality came from.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Site {
    /// One operand of one instruction.
    Operand {
        /// The instruction the operand belongs to.
        inst: Inst,
        /// The index of the operand within the instruction.
        operand: usize,
    },

    /// One parameter of one block.
    BlockParam {
        /// The block the parameter belongs to.
        block: Block,
        /// The parameter itself.
        param: Val,
    },
}

impl fmt::Debug for Site {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Operand { inst, operand } => write!(f, "operand {operand} of {inst:?}"),
            Self::BlockParam { block, param } => write!(f, "{param:?} of {block:?}"),
        }
    }
}

/// One register's worth of a value: the `index`th register of a group-resident
/// value, and the whole of any other.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Part {
    /// The value this is one register of.
    val: Val,

    /// Which of that value's registers this is.
    index: usize,
}

/// What the machine holds: the parts each location is known to contain.
///
/// A missing entry for a part is equivalent to that part having an empty set
/// (the lattice bottom).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct State {
    locs: BTreeMap<ScalarAllocation, BTreeSet<Part>>,
}

impl State {
    /// The parts `loc` holds, if it holds any.
    fn parts(&self, loc: ScalarAllocation) -> Option<&BTreeSet<Part>> {
        self.locs.get(&loc)
    }

    /// Does `loc` hold `part`?
    fn holds(&self, loc: ScalarAllocation, part: Part) -> bool {
        self.locs
            .get(&loc)
            .is_some_and(|parts| parts.contains(&part))
    }

    /// Forget the contents of every location that overlaps `loc`.
    fn clobber(&mut self, machine: &Machine, loc: ScalarAllocation) {
        self.locs
            .retain(|&other, _| !Interfere::interfere(machine, other, loc));
    }

    /// Record that `loc` holds `part`, alongside whatever else it holds.
    fn insert(&mut self, loc: ScalarAllocation, part: Part) {
        self.locs.entry(loc).or_default().insert(part);
    }

    /// Record that `loc` holds exactly `parts`.
    fn set(&mut self, loc: ScalarAllocation, parts: BTreeSet<Part>) {
        if parts.is_empty() {
            self.locs.remove(&loc);
        } else {
            self.locs.insert(loc, parts);
        }
    }

    /// Forget every part of `val`, wherever it is.
    ///
    /// A definition does this: the input is in SSA form, so anything claiming
    /// to hold `val` beforehand was left over from an earlier trip around a
    /// loop.
    fn kill(&mut self, val: Val) {
        self.locs.retain(|_, parts| {
            parts.retain(|part| part.val != val);
            !parts.is_empty()
        });
    }

    /// Meet `other` into `self`, keeping only the intersection.
    ///
    /// Returns whether `self` changed or not.
    fn meet(&mut self, other: &State) -> bool {
        let mut changed = false;
        self.locs.retain(|loc, parts| match other.locs.get(loc) {
            None => {
                changed = true;
                false
            }
            Some(theirs) => {
                let before = parts.len();
                parts.retain(|part| theirs.contains(part));
                changed |= parts.len() != before;
                !parts.is_empty()
            }
        });
        changed
    }
}

/// Which of the checker's two passes over the control-flow graph is running.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    /// Computing the fixpoint.
    Analyze,

    /// Reporting errors, if any.
    Report,
}

/// Coverage counts of various things the checker checks.
///
/// The property test asserts that random inputs reach all of it, so a checker
/// that has quietly stopped checking something fails the test.
#[derive(Debug, Default)]
#[cfg_attr(
    not(test),
    allow(dead_code, reason = "only the property test reads these")
)]
struct Stats {
    /// The allocator gave up, so the checker never ran: not what it reached
    /// but what it *missed*. Mostly unallocatable inputs check mostly nothing.
    too_many_live_regs: usize,

    reg_reg_moves: usize,
    spills: usize,
    reloads: usize,
    remats: usize,
    critical_edge_edits: usize,
    reg_group_operands: usize,
    slot_group_operands: usize,
    stack_operands: usize,
    renaming_edges: usize,
    deferred_renames: usize,
    reuse_operands: usize,
    surviving_reuse_targets: usize,
    stack_constraints: usize,
    fixed_operands: usize,
    shared_locations: usize,
    shrunk_entry_states: usize,
    entry_block_edges: usize,
    block_param_allocs: usize,
    edits_after_terminator: usize,
}

/// The abstract interpreter itself.
struct Checker<'a, F>
where
    F: InputFunction,
{
    input: &'a Input<'a, F>,
    output: &'a Output<'a>,

    /// Each block's entry state, indexed by block, or `None` for a block the
    /// analysis has not reached.
    entry_state: SecondaryMap<Block, Option<State>>,

    /// The state to assume on entry to the function, which says where its
    /// parameters are.
    seed: State,

    /// The blocks whose entry state has changed since their successors were
    /// last computed.
    worklist: Vec<Block>,

    errors: Vec<CheckerError>,

    /// The locations the instruction in hand has defined so far, and which of
    /// its operands defined each. Scratch space, cleared per instruction.
    def_locs: Vec<(usize, ScalarAllocation)>,

    /// The locations the instruction in hand has read at the point in hand,
    /// and which of its operands read each. Scratch space, cleared per point
    /// rather than per instruction, so that a definition only ever meets the
    /// reads it really races with.
    use_locs: Vec<(usize, ScalarAllocation)>,

    /// The instruction that defines each value, or `None` for a value no
    /// instruction defines, such as a block parameter, or a `Val` this function
    /// never mentions.
    ///
    /// The input function does not expose this, and the map validation builds
    /// while checking definitions is private to it, so the checker builds its
    /// own.
    defs: SecondaryMap<Val, Option<Inst>>,

    stats: Stats,
}

impl<'a, F> Checker<'a, F>
where
    F: InputFunction,
{
    fn new(input: &'a Input<'a, F>, output: &'a Output<'a>) -> Self {
        let mut checker = Checker {
            input,
            output,
            entry_state: SecondaryMap::new(None),
            seed: State::default(),
            worklist: Vec::new(),
            errors: Vec::new(),
            def_locs: Vec::new(),
            use_locs: Vec::new(),
            defs: Self::index_defs(input.func),
            stats: Stats::default(),
        };
        checker.seed = checker.seed_entry();
        checker
    }

    /// Map each value an instruction defines back to that instruction.
    ///
    /// Block parameters are left `None`: they are defined by their block's
    /// predecessors passing them, not by any one instruction.
    fn index_defs(func: &F) -> SecondaryMap<Val, Option<Inst>> {
        // Taking the block by reference keeps its borrow inside the callee,
        // where it cannot outlive the block itself.
        fn index_block<'a>(
            defs: &mut SecondaryMap<Val, Option<Inst>>,
            input_block: &impl InputBlock<'a>,
        ) {
            for (inst, input_inst) in input_block.insts() {
                for op in input_inst.operands() {
                    if let (DefUse::Def, Some(val)) = (op.kind(), op.val()) {
                        defs[val] = Some(inst);
                    }
                }
            }
        }

        let mut defs = SecondaryMap::new(None);
        for (block, _) in func.blocks() {
            index_block(&mut defs, &func.block(block));
        }
        defs
    }

    /// The state on entry to the function.
    fn seed_entry(&self) -> State {
        let func = self.input.func;
        let mut state = State::default();

        let entry = func.entry_block();
        let allocs = self.output.block_param_allocs(entry);
        for (param, alloc) in func.block(entry).params().zip(allocs) {
            let Some(alloc) = *alloc else {
                continue;
            };
            for (index, loc) in self.scalars(alloc).into_iter().enumerate() {
                state.insert(loc, Part { val: param, index });
            }
        }

        state
    }

    /// Run the fixpoint.
    fn analyze(&mut self) {
        let entry = self.input.func.entry_block();
        self.entry_state[entry] = Some(self.seed.clone());
        self.worklist.push(entry);

        while let Some(block) = self.worklist.pop() {
            self.visit_block(block, Mode::Analyze);
        }
    }

    /// After the fixpoint has completed, walk each block and report any errors.
    fn find_errors(&mut self) {
        for block in self.entry_state.keys() {
            if self.entry_state[block].is_none() {
                continue;
            }
            self.visit_block(block, Mode::Report);
        }
    }

    fn finish(self) -> Result<(), CheckerErrors> {
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(CheckerErrors {
                errors: self.errors,
            })
        }
    }

    /// Record `error`, when this is the pass that reports them.
    fn error(&mut self, mode: Mode, error: CheckerError) {
        if mode == Mode::Report {
            self.errors.push(error);
        }
    }

    /// Walk `block`: check its instructions against its entry state, run its
    /// edits and definitions, and hand the result to each of its successors.
    fn visit_block(&mut self, block: Block, mode: Mode) {
        let func = self.input.func;
        let output = self.output;
        let input_block = func.block(block);

        let mut state = self.entry_state[block]
            .clone()
            .expect("only a block that the analysis reached is ever visited");

        let mut insts_and_edits = output.block_insts_and_edits(func, block).peekable();

        // Apply the edits placed atop the block.
        let mut arrived = false;
        while insts_and_edits
            .peek()
            .is_some_and(|item| matches!(item, InstOrEdit::Edit(_)))
        {
            let Some(InstOrEdit::Edit(edit)) = insts_and_edits.next() else {
                unreachable!()
            };
            let edge_edit = match edit {
                Edit::Move(mv) => EdgeEdit::Move(mv),
                Edit::Remat(remat) => EdgeEdit::Remat(remat),
                Edit::CriticalEdge(edit) => {
                    self.error(
                        mode,
                        CheckerError::CriticalEdgeEditAtBlockEntry { block, edit },
                    );
                    continue;
                }
            };
            arrived = true;
            self.apply_edit(&mut state, block, edge_edit, mode);
        }

        // Now rename what this block's one incoming edge left to us, if any.
        if let Some((pred, index)) = self.arriving_edge(block) {
            if arrived {
                self.stats.deferred_renames += 1;
            }
            self.rename_params(&mut state, pred, index, block);
        }

        // Now that the renaming and the top-of-block edits have happened, and
        // we are about to execute the block's instructions, check the block's
        // parameters.
        self.check_block_params(&state, block, mode);

        // Now go through the block's instructions and any other edits in the
        // middle of the block.
        //
        // Edits may follow the terminator, but only where running them there
        // is the same as running them on the block's outgoing edge: one
        // successor to take, and a terminator with no operands of its own to
        // come between the edit and the edge. This is the contract
        // `move_generation::edge_position` places them under.
        let terminator = crate::liveness::block_last_inst(&input_block);
        let terminator_is_the_whole_edge =
            input_block.len_successors() == 1 && func.inst(terminator).operands_len() == 0;
        let mut past_terminator = false;
        while insts_and_edits.peek().is_some_and(|item| {
            matches!(
                item,
                InstOrEdit::Inst(_) | InstOrEdit::Edit(Edit::Move(_) | Edit::Remat(_))
            )
        }) {
            let edit = match insts_and_edits.next().unwrap() {
                InstOrEdit::Inst(inst) => {
                    self.check_inst(&mut state, inst, mode);
                    past_terminator |= inst == terminator;
                    continue;
                }
                InstOrEdit::Edit(Edit::Move(mv)) => EdgeEdit::Move(mv),
                InstOrEdit::Edit(Edit::Remat(remat)) => EdgeEdit::Remat(remat),
                InstOrEdit::Edit(Edit::CriticalEdge(_)) => {
                    unreachable!("the loop condition excludes critical-edge edits")
                }
            };
            if past_terminator {
                self.stats.edits_after_terminator += 1;
                if !terminator_is_the_whole_edge {
                    self.error(
                        mode,
                        CheckerError::EditAfterTerminator {
                            block,
                            terminator,
                            edit,
                        },
                    );
                }
            }
            self.apply_edit(&mut state, block, edit, mode);
        }

        // Finally, collect the block's outgoing critical-edge edits, bucketing
        // them by `succ`th successor.
        let mut critical_edge_edits = alloc::vec![Vec::new(); input_block.len_successors()];
        for item in insts_and_edits {
            match item {
                InstOrEdit::Edit(Edit::CriticalEdge(CriticalEdgeEdit { target, succ, edit })) => {
                    let names_the_edge = input_block.successors().nth(succ) == Some(target);
                    match critical_edge_edits.get_mut(succ) {
                        Some(edits) if names_the_edge => edits.push(edit),
                        _ => self.error(
                            mode,
                            CheckerError::BadCriticalEdgeSuccessor {
                                block,
                                succ,
                                target,
                            },
                        ),
                    }
                    self.stats.critical_edge_edits += 1;
                }
                item => self.error(
                    mode,
                    CheckerError::ItemAfterCriticalEdgeEdits { block, item },
                ),
            }
        }

        // And then check each outgoing edge.
        //
        // We simulate critical-edge splitting by cloning the state for each
        // edge, so that the edge's critical-edge edits, if any, are only
        // applied on that edge.
        for (index, succ) in input_block.successors().enumerate() {
            let mut out = state.clone();
            for &edit in &critical_edge_edits[index] {
                self.apply_edit(&mut out, block, edit, mode);
            }
            if self.arriving_edge(succ).is_none() {
                self.rename_params(&mut out, block, index, succ);
            }
            if succ == func.entry_block() {
                self.stats.entry_block_edges += 1;
            }

            // Only the first pass propagates: the second is reporting against
            // states the first already settled, and must not disturb them.
            if mode == Mode::Analyze {
                self.meet_into(succ, out);
            }
        }
    }

    /// Check that each of `block`'s parameters really is where
    /// `Output::block_param_allocs` says it arrives.
    fn check_block_params(&mut self, state: &State, block: Block, mode: Mode) {
        if mode != Mode::Report {
            return;
        }

        let func = self.input.func;
        let output = self.output;
        let machine = self.input.machine;

        let expected = func.block(block).len_params();
        let actual = output.block_param_allocs(block).len();
        if expected != actual {
            self.error(
                mode,
                CheckerError::WrongBlockParamAllocCount {
                    block,
                    expected,
                    actual,
                },
            );
        }

        // Where each parameter seen so far arrives, so that the next one can
        // be checked against them.
        let mut param_locs: Vec<(Val, ScalarAllocation)> = Vec::new();

        for (param, &alloc) in func
            .block(block)
            .params()
            .zip(output.block_param_allocs(block))
        {
            let Some(alloc) = alloc else {
                continue;
            };
            self.stats.block_param_allocs += 1;

            // The same shape and class questions `check_constraints` asks of
            // an operand, against the parameter's own class.
            let site = Site::BlockParam { block, param };
            let scalars = self.scalars(alloc);
            self.check_alloc_legality(site, param, alloc, &scalars, mode);
            self.check_reg_class(site, param.reg_class(self.input), alloc, mode);

            // A parameter is a definition, so it gets the definition rule too.
            self.check_def_is_allocatable(site, &scalars, mode);

            for (index, loc) in scalars.into_iter().enumerate() {
                if !state.holds(loc, Part { val: param, index }) {
                    self.error(
                        mode,
                        CheckerError::MisplacedBlockParam {
                            block,
                            param,
                            alloc,
                        },
                    );
                }

                // Exclusivity, which the check above does not give: however
                // many places one parameter is in, two parameters in one place
                // is always wrong because (a) a caller cannot deliver two
                // arguments in one register, and (b) elsewhere it is two
                // interfering live-ins.
                let conflict = param_locs
                    .iter()
                    .find(|&&(other, arrived)| {
                        other != param && Interfere::interfere(machine, arrived, loc)
                    })
                    .map(|&(other, _)| other);
                if let Some(other) = conflict {
                    self.error(
                        mode,
                        CheckerError::ConflictingBlockParams {
                            block,
                            param,
                            other,
                            loc,
                        },
                    );
                }
                param_locs.push((param, loc));
            }
        }
    }

    /// Meet the state arriving from a predecessor into `succ`'s entry state,
    /// and queue `succ` when that changed anything.
    fn meet_into(&mut self, succ: Block, state: State) {
        let slot = &mut self.entry_state[succ];
        match slot {
            None => {
                *slot = Some(state);
                self.worklist.push(succ);
            }
            Some(existing) => {
                if existing.meet(&state) {
                    self.stats.shrunk_entry_states += 1;
                    self.worklist.push(succ);
                }
            }
        }
    }

    /// The edge `block` takes its arriving edits from, as a predecessor and an
    /// outgoing edge index, if it takes any.
    fn arriving_edge(&self, block: Block) -> Option<(Block, usize)> {
        let func = self.input.func;
        let input_block = func.block(block);
        if input_block.len_predecessors() != 1 || block == func.entry_block() {
            return None;
        }
        let pred = input_block.predecessors().next()?;
        let index = func
            .block(pred)
            .successors()
            .position(|succ| succ == block)?;
        Some((pred, index))
    }

    /// Rename the arguments `pred`'s `index`th edge passes into the parameters
    /// they define.
    fn rename_params(&mut self, state: &mut State, pred: Block, index: usize, succ: Block) {
        let func = self.input.func;
        let input_pred = func.block(pred);
        let input_succ = func.block(succ);

        let mut params = Vec::new();
        let mut renamed = Vec::new();

        debug_assert_eq!(
            input_succ.len_params(),
            input_pred.len_successor_block_args(index),
            "checked by input validation"
        );
        for (param, arg) in input_succ
            .params()
            .zip(input_pred.successor_block_args(index))
        {
            params.push(param);
            for (&loc, parts) in &state.locs {
                for part in parts {
                    if part.val == arg {
                        renamed.push((
                            loc,
                            Part {
                                val: param,
                                index: part.index,
                            },
                        ));
                    }
                }
            }
        }

        if params.is_empty() {
            return;
        }

        for param in params {
            state.kill(param);
        }
        for (loc, part) in &renamed {
            state.insert(*loc, *part);
        }

        if !renamed.is_empty() {
            self.stats.renaming_edges += 1;
        }
    }

    /// Run one edit, whether it sits inside a block or on an edge leaving it,
    /// against `state`.
    fn apply_edit(&mut self, state: &mut State, block: Block, edit: EdgeEdit, mode: Mode) {
        let machine = self.input.machine;

        let (from, to) = match edit {
            EdgeEdit::Remat(Remat { val, dest }) => {
                self.stats.remats += 1;

                if self.input.func.value(val).remat_cost().is_none() {
                    self.error(mode, CheckerError::NotRematerializable { block, val });
                }
                if val.num_regs(self.input) != 1 {
                    self.error(mode, CheckerError::RematOfRegGroup { block, val });
                }

                // Rematerializations (currently) may have no inputs.
                let def = self.defs[val];
                let derived = match def {
                    None => true,
                    Some(def) => self
                        .input
                        .func
                        .inst(def)
                        .operands()
                        .any(|op| op.kind() == DefUse::Use),
                };
                if derived {
                    self.error(mode, CheckerError::RematOfDerivedValue { block, val, def });
                }

                // A rematerialization names its value, so unlike a move it is
                // held to that value's own class rather than only to its bank.
                let class = val.reg_class(self.input);
                if !class.member_set(machine).contains(dest) {
                    self.error(
                        mode,
                        CheckerError::RematNotInRegClass {
                            block,
                            val,
                            class,
                            reg: dest,
                        },
                    );
                }

                // A rematerialization computes the value from nothing, so the
                // whole of it lands in `dest` however the state got here.
                let dest = ScalarAllocation::Reg(dest);
                state.clobber(machine, dest);
                state.insert(dest, Part { val, index: 0 });
                return;
            }

            EdgeEdit::Move(mov) => {
                self.check_move_is_well_formed(block, mov, mode);
                match mov {
                    Move::RegReg { from, to } => {
                        self.stats.reg_reg_moves += 1;
                        (ScalarAllocation::Reg(from), ScalarAllocation::Reg(to))
                    }
                    Move::Spill { from, to } => {
                        self.stats.spills += 1;
                        (ScalarAllocation::Reg(from), ScalarAllocation::Stack(to))
                    }
                    Move::Reload { from, to } => {
                        self.stats.reloads += 1;
                        (ScalarAllocation::Stack(from), ScalarAllocation::Reg(to))
                    }
                }
            }
        };

        // A move copies whatever the source holds, including nothing at all,
        // so a later read of the destination is then an error.
        let parts = state.parts(from).cloned().unwrap_or_default();

        // Writing a register the allocator does not own is how a value reaches
        // an operand pinned to it, so the destination is judged by what it
        // receives: only a value whose own class holds the register could have
        // been pinned there.
        if let ScalarAllocation::Reg(reg) = to {
            if reg.is_non_allocatable(machine) {
                if parts.is_empty() {
                    self.error(
                        mode,
                        CheckerError::MoveIntoNonAllocatableReg {
                            block,
                            val: None,
                            reg,
                        },
                    );
                }
                for part in &parts {
                    if !part
                        .val
                        .reg_class(self.input)
                        .member_set(machine)
                        .contains(reg)
                    {
                        self.error(
                            mode,
                            CheckerError::MoveIntoNonAllocatableReg {
                                block,
                                val: Some(part.val),
                                reg,
                            },
                        );
                    }
                }
            }
        }

        // Every value moved must be able to live where the move puts it.
        for part in &parts {
            let val = part.val;
            let expected = val.reg_bank(self.input);
            match to {
                ScalarAllocation::Reg(reg) => {
                    let actual = reg.bank(machine);
                    if actual != expected {
                        self.error(
                            mode,
                            CheckerError::BadMoveBank {
                                block,
                                val,
                                expected,
                                actual,
                            },
                        );
                    }
                }
                ScalarAllocation::Stack(slot) => {
                    let expected = expected.size(machine);
                    let Some(actual) = self.output.try_spill_slot(slot) else {
                        self.error(mode, CheckerError::NoSuchSpillSlot { slot });
                        continue;
                    };
                    if actual != expected {
                        self.error(
                            mode,
                            CheckerError::WrongMoveSlotSize {
                                block,
                                val,
                                slot,
                                expected,
                                actual,
                            },
                        );
                    }
                }
            }
        }

        state.clobber(machine, to);
        state.set(to, parts);
    }

    /// Check that a move's two ends can hold the same thing, whatever that
    /// turns out to be.
    fn check_move_is_well_formed(&mut self, block: Block, mov: Move, mode: Mode) {
        let machine = self.input.machine;
        match mov {
            Move::RegReg { from, to } => {
                let (from, to) = (from.bank(machine), to.bank(machine));
                if from != to {
                    self.error(
                        mode,
                        CheckerError::MismatchedMoveBanks {
                            block,
                            mov,
                            from,
                            to,
                        },
                    );
                }
            }
            // A spill writes a whole register and a reload reads a whole slot,
            // so either way the slot is the size of the register's bank.
            Move::Spill { from, to } => {
                self.check_move_slot_size(block, mov, to, from.bank(machine), mode)
            }
            Move::Reload { from, to } => {
                self.check_move_slot_size(block, mov, from, to.bank(machine), mode)
            }
        }
    }

    /// Check that `slot` is the size of a register of `bank`, for a move with
    /// one end in each.
    fn check_move_slot_size(
        &mut self,
        block: Block,
        mov: Move,
        slot: SpillSlot,
        bank: RegBank,
        mode: Mode,
    ) {
        let expected = bank.size(self.input.machine);
        let Some(actual) = self.output.try_spill_slot(slot) else {
            self.error(mode, CheckerError::NoSuchSpillSlot { slot });
            return;
        };
        if actual != expected {
            self.error(
                mode,
                CheckerError::MismatchedMoveSlotSize {
                    block,
                    mov,
                    slot,
                    expected,
                    actual,
                },
            );
        }
    }

    /// Check one instruction, and run its definitions against `state`.
    fn check_inst(&mut self, state: &mut State, inst: Inst, mode: Mode) {
        let func = self.input.func;
        let output = self.output;

        let operands = func.inst(inst).operands().collect::<Vec<_>>();
        let allocs = output.inst_allocs(inst);
        if allocs.len() != operands.len() {
            self.error(
                mode,
                CheckerError::WrongAllocCount {
                    inst,
                    expected: operands.len(),
                    actual: allocs.len(),
                },
            );
            return;
        }

        // Each operand's allocation, split into single locations: a register
        // group into its members, a slot group into its slots.
        let scalars = allocs
            .iter()
            .map(|&alloc| self.scalars(alloc))
            .collect::<Vec<_>>();

        for (i, &op) in operands.iter().enumerate() {
            self.check_constraints(inst, i, op, allocs, &scalars[i], mode);
        }

        self.def_locs.clear();
        self.use_locs.clear();

        // The instruction reads and writes (at the same time) in two phases:
        // early and late.

        // Early uses. Run all these first, before defs, so that we can detect
        // conflicting defs via `self.use_locs`.
        for (i, &op) in operands.iter().enumerate() {
            if op.pos().is_early() && op.kind() == DefUse::Use {
                self.read_operand(state, inst, i, op, &scalars[i], mode);
            }
        }

        // Early defs.
        for (i, &op) in operands.iter().enumerate() {
            if op.pos().is_early() && op.kind() == DefUse::Def {
                self.write_operand(state, inst, i, op, &scalars[i], mode);
            }
        }

        // The early uses and any early defs that could conflict with them have
        // all completed, so we can clear them now.
        self.use_locs.clear();

        // Late uses. These are evaluated before defs, like above.
        for (i, &op) in operands.iter().enumerate() {
            if op.pos().is_late() && op.kind() == DefUse::Use {
                self.read_operand(state, inst, i, op, &scalars[i], mode);
            }
        }

        // Coverage, counted before the writes land: a tie whose reused value is
        // also elsewhere is the case span construction splits around, and that
        // copy is what the split leaves behind.
        if mode == Mode::Report {
            for (i, &op) in operands.iter().enumerate() {
                let OperandConstraint::Reuse(target) = op.constraint() else {
                    continue;
                };
                let Some(target_val) = operands.get(target).and_then(|op| op.val()) else {
                    continue;
                };
                let survives = state.locs.iter().any(|(loc, parts)| {
                    !scalars[i].contains(loc) && parts.iter().any(|p| p.val == target_val)
                });
                if survives {
                    self.stats.surviving_reuse_targets += 1;
                }
            }
        }

        // Late writes.
        for (i, &op) in operands.iter().enumerate() {
            if op.pos().is_late() && op.kind() == DefUse::Def {
                self.write_operand(state, inst, i, op, &scalars[i], mode);
            }
        }
    }

    /// The single locations that `alloc` is made of, in order.
    fn scalars(&self, alloc: Allocation) -> Vec<ScalarAllocation> {
        match alloc {
            Allocation::Reg(RegAllocation::Reg(reg)) => Vec::from([ScalarAllocation::Reg(reg)]),
            Allocation::Reg(RegAllocation::RegGroup(group)) => group
                .members(self.input.machine)
                .iter()
                .map(|&reg| ScalarAllocation::Reg(reg))
                .collect(),
            Allocation::Stack(StackAllocation::SpillSlot(slot)) => {
                Vec::from([ScalarAllocation::Stack(slot)])
            }
            Allocation::Stack(StackAllocation::SpillSlotGroup(group)) => self
                .output
                .spill_slot_group_members(group)
                .map(ScalarAllocation::Stack)
                .collect(),
        }
    }

    /// Check everything about where an operand was placed that does not depend
    /// on what the machine holds.
    fn check_constraints(
        &mut self,
        inst: Inst,
        i: usize,
        op: Operand,
        allocs: &[Allocation],
        scalars: &[ScalarAllocation],
        mode: Mode,
    ) {
        let machine = self.input.machine;
        let alloc = allocs[i];
        let site = Site::Operand { inst, operand: i };

        match alloc {
            Allocation::Reg(RegAllocation::Reg(_)) => {}
            Allocation::Reg(RegAllocation::RegGroup(_)) => self.stats.reg_group_operands += 1,
            Allocation::Stack(StackAllocation::SpillSlot(_)) => self.stats.stack_operands += 1,
            Allocation::Stack(StackAllocation::SpillSlotGroup(_)) => {
                self.stats.stack_operands += 1;
                self.stats.slot_group_operands += 1;
            }
        }

        // An operand naming no value names a register the allocator does not
        // own, and validation has already rejected every other shape. There is
        // no value here whose class, size, or liveness could be wrong, so all
        // that is left to check is that the allocation is the register the
        // operand asked for.
        let Some(val) = op.val() else {
            if let OperandConstraint::Reg(class) = op.constraint() {
                if class.is_singleton(machine) {
                    self.stats.fixed_operands += 1;
                }
                if matches!(alloc, Allocation::Reg(_)) {
                    self.check_reg_class(site, class, alloc, mode);
                } else {
                    self.error(mode, CheckerError::NotAReg { inst, operand: i });
                }
            }
            return;
        };

        self.check_alloc_legality(site, val, alloc, scalars, mode);

        match op.constraint() {
            OperandConstraint::Any => {
                // Nothing pins down where the operand goes, but a register
                // allocation must still be one the value can live in.
                let class = val.reg_class(self.input);
                self.check_reg_class(site, class, alloc, mode);
            }

            OperandConstraint::Reg(class) => {
                if class.is_singleton(machine) {
                    self.stats.fixed_operands += 1;
                }
                if matches!(alloc, Allocation::Reg(_)) {
                    self.check_reg_class(site, class, alloc, mode);
                } else {
                    self.error(mode, CheckerError::NotAReg { inst, operand: i });
                }
            }

            OperandConstraint::Stack => {
                self.stats.stack_constraints += 1;
                if !matches!(alloc, Allocation::Stack(_)) {
                    self.error(mode, CheckerError::NotOnStack { inst, operand: i });
                }
            }

            OperandConstraint::Reuse(target) => {
                self.stats.reuse_operands += 1;
                if allocs.get(target) != Some(&alloc) {
                    self.error(
                        mode,
                        CheckerError::ReuseMismatch {
                            inst,
                            operand: i,
                            alloc,
                            target,
                            target_alloc: allocs.get(target).copied(),
                        },
                    );
                }

                // A tie is a register constraint too: `reuse_aware_constraint`
                // strengthens both halves to `Reg(class)` before the allocator
                // sees them, and we check that here.
                if matches!(alloc, Allocation::Reg(_)) {
                    self.check_reg_class(site, val.reg_class(self.input), alloc, mode);
                } else {
                    self.error(mode, CheckerError::NotAReg { inst, operand: i });
                }
            }
        }
    }

    /// Check the shape of `val`'s allocation: one location per register, a
    /// group exactly when the value lives in one, and slots of the value's
    /// size.
    fn check_alloc_legality(
        &mut self,
        site: Site,
        val: Val,
        alloc: Allocation,
        scalars: &[ScalarAllocation],
        mode: Mode,
    ) {
        let machine = self.input.machine;

        // The allocation is made of one location per register the value
        // occupies...
        let expected = val.num_regs(self.input);
        if scalars.len() != expected {
            let actual = scalars.len();
            self.error(
                mode,
                match site {
                    Site::Operand { inst, operand } => CheckerError::WrongScalarCount {
                        inst,
                        operand,
                        expected,
                        actual,
                    },
                    Site::BlockParam { block, param } => CheckerError::BlockParamWrongScalarCount {
                        block,
                        param,
                        expected,
                        actual,
                    },
                },
            );
        }

        // ...and it is a group exactly when the value's own class is one of
        // register groups.
        let wants_group = val.reg_class(self.input).group_size(machine).is_some();
        let is_group = matches!(
            alloc,
            Allocation::Reg(RegAllocation::RegGroup(_))
                | Allocation::Stack(StackAllocation::SpillSlotGroup(_))
        );
        if wants_group != is_group {
            self.error(
                mode,
                match site {
                    Site::Operand { inst, operand } => {
                        CheckerError::GroupMismatch { inst, operand }
                    }
                    Site::BlockParam { block, param } => CheckerError::BlockParamGroupMismatch {
                        block,
                        param,
                        alloc,
                    },
                },
            );
        }

        // A slot holding the value has to be the size of one of its registers.
        let expected = val.reg_bank(self.input).size(machine);
        for &loc in scalars {
            let ScalarAllocation::Stack(slot) = loc else {
                continue;
            };
            let Some(actual) = self.output.try_spill_slot(slot) else {
                self.error(mode, CheckerError::NoSuchSpillSlot { slot });
                continue;
            };
            if actual != expected {
                self.error(
                    mode,
                    match site {
                        Site::Operand { inst, operand } => CheckerError::WrongSpillSlotSize {
                            inst,
                            operand,
                            slot,
                            expected,
                            actual,
                        },
                        Site::BlockParam { block, param } => {
                            CheckerError::BlockParamWrongSpillSlotSize {
                                block,
                                param,
                                slot,
                                expected,
                                actual,
                            }
                        }
                    },
                );
            }
        }
    }

    /// Check that a register allocation is one of `class`'s members, which
    /// already implies it may be allocated at all.
    fn check_reg_class(&mut self, site: Site, class: RegClass, alloc: Allocation, mode: Mode) {
        let machine = self.input.machine;
        match (class.members(machine), alloc) {
            (_, Allocation::Stack(_)) => {}

            (RegClassMembers::Regs(_), Allocation::Reg(RegAllocation::Reg(reg))) => {
                if !class.member_set(machine).contains(reg) {
                    self.error(
                        mode,
                        CheckerError::NotInRegClass {
                            site,
                            class,
                            alloc: RegAllocation::Reg(reg),
                        },
                    );
                }
            }

            (RegClassMembers::Groups(groups), Allocation::Reg(RegAllocation::RegGroup(group))) => {
                if !groups.contains(&group) {
                    self.error(
                        mode,
                        CheckerError::NotInRegClass {
                            site,
                            class,
                            alloc: RegAllocation::RegGroup(group),
                        },
                    );
                }
            }

            // A group where the class wants a single register, or vice versa.
            // Validation makes an operand's class a subset of its value's, so
            // `GroupMismatch` above has already reported this disagreement.
            (RegClassMembers::Regs(_), Allocation::Reg(RegAllocation::RegGroup(_)))
            | (RegClassMembers::Groups(_), Allocation::Reg(RegAllocation::Reg(_))) => {}
        }
    }

    /// Check that a definition landed in a register the allocator is allowed
    /// to hand out.
    ///
    /// A non-allocatable register may be read (pinning an operand to `sp` is
    /// exactly what putting one in a class is for). It cannot be the home a
    /// definition gives its value because the allocator does not own it or
    /// track its interference.
    fn check_def_is_allocatable(&mut self, site: Site, scalars: &[ScalarAllocation], mode: Mode) {
        let machine = self.input.machine;
        for &loc in scalars {
            if let ScalarAllocation::Reg(reg) = loc {
                if reg.is_non_allocatable(machine) {
                    self.error(mode, CheckerError::DefInNonAllocatableReg { site, reg });
                }
            }
        }
    }

    /// Check that an operand's allocation holds the value the operand reads.
    fn read_operand(
        &mut self,
        state: &State,
        inst: Inst,
        i: usize,
        op: Operand,
        scalars: &[ScalarAllocation],
        mode: Mode,
    ) {
        // An operand naming no value reads a register the allocator does not
        // own, so what it holds is the client's own business and there is
        // nothing here to compare against.
        let Some(val) = op.val() else {
            return;
        };

        for (index, &loc) in scalars.iter().enumerate() {
            self.use_locs.push((i, loc));

            let mut actual = state
                .parts(loc)
                .map(|parts| parts.iter().map(|part| part.val).collect::<Vec<_>>())
                .unwrap_or_default();
            actual.dedup();

            if mode == Mode::Report && actual.len() > 1 {
                self.stats.shared_locations += 1;
            }

            if !state.holds(loc, Part { val, index }) {
                self.error(
                    mode,
                    CheckerError::WrongValue {
                        inst,
                        operand: i,
                        val,
                        index,
                        loc,
                        actual,
                    },
                );
            }
        }
    }

    /// Run an operand's definition against `state`, and check that no other
    /// definition of the same instruction writes where it writes.
    fn write_operand(
        &mut self,
        state: &mut State,
        inst: Inst,
        i: usize,
        op: Operand,
        scalars: &[ScalarAllocation],
        mode: Mode,
    ) {
        let machine = self.input.machine;
        // Validation rejects a definition that names no value.
        let val = op.val().unwrap();

        self.check_def_is_allocatable(Site::Operand { inst, operand: i }, scalars, mode);

        // Check for conflicting definitions.
        for &loc in scalars {
            let conflict = self
                .def_locs
                .iter()
                .find(|&&(_, written)| Interfere::interfere(machine, written, loc))
                .map(|&(other, _)| other);
            if let Some(other) = conflict {
                self.error(
                    mode,
                    CheckerError::ConflictingDef {
                        inst,
                        operand: i,
                        other,
                        loc,
                    },
                );
            }

            // And for a definition landing on something this instruction reads
            // at the same point, which destroys the read value rather than
            // merely sharing a location with it.
            let clobbered = self
                .use_locs
                .iter()
                .find(|&&(_, read)| Interfere::interfere(machine, read, loc))
                .map(|&(other, _)| other);
            if let Some(other) = clobbered {
                self.error(
                    mode,
                    CheckerError::DefClobbersUse {
                        inst,
                        operand: i,
                        other,
                        loc,
                    },
                );
            }

            self.def_locs.push((i, loc));
        }

        // The definition destroys what its locations held.
        for &loc in scalars {
            state.clobber(machine, loc);
        }

        // Because the input is in SSA, anything already claiming to hold the
        // value is stale
        state.kill(val);

        // Apply the definitions' writes.
        for (index, &loc) in scalars.iter().enumerate() {
            state.insert(loc, Part { val, index });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Entity as _,
        context::{Context, WhichContext},
        error::Error,
        input::{Position, RematCost},
        machine::{RegClassMembers, RegGroup},
        test::{TestInput, TestMachine},
    };
    use core::sync::atomic::{AtomicUsize, Ordering};
    use mutatis::{
        check::{Check, CheckResult},
        mutators as m,
    };
    use std::{format, string::String, vec, vec::Vec};

    /// Allocate `allocated`, and check that allocation against `checked`.
    ///
    /// The two are the same function everywhere but in the negative tests,
    /// which check an allocation against a perturbed copy so that it really is
    /// wrong for the function it is checked against.
    ///
    /// Returns what the checker reached, so the property check below can tell
    /// whether its inputs were about anything.
    fn check_against(allocated: &TestInput, checked: &TestInput) -> Result<Stats, String> {
        let mut context = Context::new();
        assert!(context.is_reset());

        let stats = allocated.with_input(|input| -> Result<Stats, String> {
            let output = match crate::run(&mut context, input) {
                Ok(output) => output,
                // Not every function fits on every machine, which is not the
                // checker's problem --- but a run that skips too many inputs
                // checks too little, so record it.
                Err(Error::TooManyLiveRegs) => {
                    return Ok(Stats {
                        too_many_live_regs: 1,
                        ..Default::default()
                    });
                }
                Err(e) => return Err(format!("allocation failed: {e:?}")),
            };

            checked.with_input(|input| {
                // Driven by hand rather than through `check`, so that the
                // property check can read the stats out of it.
                let mut checker = Checker::new(input, &output);
                checker.analyze();
                checker.find_errors();
                let stats = core::mem::take(&mut checker.stats);
                checker.finish().map_err(|e| format!("{e:?}"))?;
                Ok(stats)
            })
        })?;

        // The pipeline leaves nothing behind that a reset does not clean up.
        context.reset();
        assert!(context.is_reset());

        Ok(stats)
    }

    /// Allocate `test_input` and check the allocation.
    fn check_allocation(test_input: &TestInput) -> Result<Stats, String> {
        check_against(test_input, test_input)
    }

    /// Every operand of `test_input`, with the instruction and index that name
    /// it.
    fn operands(test_input: &TestInput) -> Vec<(Inst, usize, Operand)> {
        let mut operands = Vec::new();
        test_input.with_input(|input| {
            for (_, block) in input.func.blocks() {
                for (inst, input_inst) in block.insts() {
                    for (i, op) in input_inst.operands().enumerate() {
                        operands.push((inst, i, op));
                    }
                }
            }
        });
        operands
    }

    /// The inputs the property check starts from.
    fn seeds() -> Vec<TestInput> {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let group_class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        vec![
            TestInput::default(),
            TestInput::with_spilled_merge_param(),
            TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]),
            TestInput::with_use_constraints(&[OperandConstraint::Stack]),
            TestInput::with_use_constraints(&[
                OperandConstraint::Stack,
                OperandConstraint::Reg(class),
            ]),
            TestInput::with_group_use_constraints(&[
                OperandConstraint::Stack,
                OperandConstraint::Reg(group_class),
            ]),
            TestInput::with_reuse_def(OperandConstraint::Any),
            TestInput::with_reuse_of_a_surviving_value(),
            TestInput::with_two_reads_and_a_reuse_of_a_surviving_value(),
            TestInput::with_a_fixed_read_beside_a_reuse_of_a_surviving_value(),
            TestInput::with_a_pinned_read_before_a_reuse_that_reads_twice(),
            TestInput::with_a_reuse_of_a_live_in_value(),
            TestInput::with_two_reuses_at_one_point(),
            TestInput::with_two_reuses_of_a_dying_value(),
            TestInput::with_block_arg_constraints(OperandConstraint::Any, OperandConstraint::Stack),
            TestInput::with_stack_param_and_arg(),
            TestInput::with_a_rematerialized_block_arg(),
            TestInput::with_two_uses_of_different_values(),
            TestInput::with_a_critical_edge(),
            TestInput::with_values_in_two_banks_spilled_and_reloaded(),
            TestInput::with_an_entry_param_read_two_ways(),
            TestInput::with_two_entry_params(),
            TestInput::with_entry_params_in_two_banks(),
            TestInput::with_a_self_looping_entry_block(),
            TestInput::with_a_move_after_an_unconditional_branch(),
            TestInput::with_a_val_less_read_of_a_non_allocatable_reg(),
            TestInput::with_a_reuse_of_a_pinned_read(),
        ]
    }

    /// The allocator's output is a correct allocation of its input.
    ///
    /// The counters make sure the inputs reached the cases the checker is
    /// about. They are counted here rather than in a check of their own: a
    /// separate check is a separate random walk, whose coverage would say
    /// nothing about the inputs *this* one saw.
    #[test]
    fn checker_properties() -> CheckResult<TestInput> {
        /// The share of inputs the allocator may give up on before this check
        /// is judged to cover too little.
        ///
        /// Measured at 36% when this was written; the headroom is deliberately
        /// loose, to catch a change that makes inputs wildly harder to
        /// allocate rather than to pin the rate down.
        const SKIP_CEILING_PERCENT: usize = 60;
        macro_rules! counters {
            ($($name:ident : $field:ident = $what:expr,)*) => {
                $(static $name: AtomicUsize = AtomicUsize::new(0);)*
                $($name.store(0, Ordering::Relaxed);)*

                // How many inputs were tried, and how many of them the
                // allocator gave up on before the checker saw anything.
                static ITERS: AtomicUsize = AtomicUsize::new(0);
                static SKIPPED: AtomicUsize = AtomicUsize::new(0);
                ITERS.store(0, Ordering::Relaxed);
                SKIPPED.store(0, Ordering::Relaxed);

                let result = Check::new().iters(20_000).run_with(
                    m::default::<TestInput>(),
                    seeds(),
                    |test_input: &TestInput| -> Result<(), String> {
                        let stats = check_allocation(test_input)?;
                        ITERS.fetch_add(1, Ordering::Relaxed);
                        SKIPPED.fetch_add(stats.too_many_live_regs, Ordering::Relaxed);
                        $($name.fetch_add(stats.$field, Ordering::Relaxed);)*
                        Ok(())
                    },
                );

                if result.is_ok() {
                    $(assert!(
                        $name.load(Ordering::Relaxed) > 0,
                        "no input produced {}, so the checker's properties are vacuous",
                        $what,
                    );)*

                    // A ceiling rather than a floor: an input that does not
                    // fit on the test machine is not checked at all, so a
                    // change making most of them unallocatable would leave
                    // every counter above positive while this check covered
                    // almost nothing. The threshold is a few times the rate
                    // measured when this was written, to catch a regression in
                    // register pressure and not the noise of a random walk.
                    let iters = ITERS.load(Ordering::Relaxed);
                    let skipped = SKIPPED.load(Ordering::Relaxed);
                    assert!(
                        skipped * 100 <= iters * SKIP_CEILING_PERCENT,
                        "the allocator gave up on {skipped} of {iters} inputs, over the \
                         {SKIP_CEILING_PERCENT}% this check tolerates: almost nothing was \
                         actually checked",
                    );
                }

                result
            };
        }

        counters! {
            REG_REG_MOVES: reg_reg_moves = "a register-to-register move",
            SPILLS: spills = "a spill",
            RELOADS: reloads = "a reload",
            REMATS: remats = "a rematerialization",
            CRITICAL_EDGE_EDITS: critical_edge_edits = "an edit on a critical edge",
            REG_GROUP_OPERANDS: reg_group_operands = "an operand in a register group",
            SLOT_GROUP_OPERANDS: slot_group_operands = "an operand in a group of spill slots",
            STACK_OPERANDS: stack_operands = "an operand on the stack",
            RENAMING_EDGES: renaming_edges = "an edge that renames a block parameter",
            DEFERRED_RENAMES: deferred_renames =
                "a block that hosts its edge's edits, and so renames its parameters after them",
            REUSE_OPERANDS: reuse_operands = "an operand that reuses another",
            SURVIVING_REUSE_TARGETS: surviving_reuse_targets =
                "a reuse whose reused value is still live in another location",
            STACK_CONSTRAINTS: stack_constraints = "an operand constrained to the stack",
            FIXED_OPERANDS: fixed_operands = "an operand pinned to one register",
            SHARED_LOCATIONS: shared_locations = "a location holding more than one value",
            SHRUNK_ENTRY_STATES: shrunk_entry_states = "a block whose entry state shrank",
            ENTRY_BLOCK_EDGES: entry_block_edges = "an edge arriving at the entry block",
            BLOCK_PARAM_ALLOCS: block_param_allocs =
                "a block parameter the results give a location",
            EDITS_AFTER_TERMINATOR: edits_after_terminator =
                "an edit placed after a block's terminator",
        }
    }

    /// Each fixture the property check starts from allocates correctly, which
    /// is worth having separately because a failure here is a much smaller
    /// reproducer.
    ///
    /// A seed the allocator gives up on is a failure too: a seed that does not
    /// fit on its own machine never puts the checker in front of the shape it
    /// exists for, and the mutations from it inherit the problem.
    #[test]
    fn the_seeds_all_check_out() {
        for (i, seed) in seeds().into_iter().enumerate() {
            let stats =
                check_allocation(&seed).unwrap_or_else(|e| panic!("seed {i} failed to check: {e}"));
            assert_eq!(
                stats.too_many_live_regs, 0,
                "seed {i} does not fit on its own machine, so nothing about it was checked",
            );
        }
    }

    /// Tying a definition to a read of a value that survives the instruction
    /// costs no register beyond the two the value and the definition need.
    ///
    /// The split cuts the read value into a piece before the tie, the copy the
    /// definition overwrites, and the survivor. The first is where the
    /// pessimizations live: reaching past the instruction it overlaps the
    /// other two, and pushed while empty it holds a location nothing reads.
    /// Either way the fixture stops fitting on its slackless machine.
    #[test]
    fn a_reuse_of_a_surviving_value_costs_no_extra_register() {
        for (i, test_input) in [
            // The tie reads the value twice, so the piece before it must hand
            // both reads over rather than keeping the first.
            TestInput::with_two_reads_and_a_reuse_of_a_surviving_value(),
            // The value arrives live-in at the block holding the tie, so the
            // piece before the tie is empty.
            TestInput::with_a_reuse_of_a_live_in_value(),
            // Two ties at one point, so the piece before the second is empty:
            // the first has already taken everything up to here.
            TestInput::with_two_reuses_at_one_point(),
            // Two ties at one point on a dying value still need a copy each:
            // the definitions overwriting the reads cannot share a register.
            TestInput::with_two_reuses_of_a_dying_value(),
        ]
        .into_iter()
        .enumerate()
        {
            let stats = check_allocation(&test_input)
                .unwrap_or_else(|e| panic!("fixture {i} failed to check: {e}"));
            assert_eq!(
                stats.too_many_live_regs, 0,
                "fixture {i} should fit on its machine without the reuse split \
                 reserving a location for nothing",
            );
        }
    }

    /// The only value of `test_input`, which the single-value fixtures define
    /// first.
    fn first_val(test_input: &TestInput) -> Val {
        test_input.with_input(|input| input.func.values().next().expect("a value").0)
    }

    /// A tied definition really is in the same place as the operand it names:
    /// the check live span construction's reuse split exists to satisfy, and
    /// so the one that most needs a test.
    #[test]
    fn checks_that_a_reuse_landed_on_its_target() {
        let mut test_input = TestInput::with_two_uses_of_different_values();
        check_allocation(&test_input).unwrap();

        // The fixture pins its two reads to different registers, so claiming
        // the first reuses the second is a claim the allocation does not meet.
        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, i, op)| i == 0 && op.kind() == DefUse::Use)
            .expect("the fixture reads two values in one instruction");

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, i) =
            Operand::new(op.pos(), op.kind(), OperandConstraint::Reuse(1), op.val());

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("reuses operand 1"), "{error}");
    }

    /// An operand pinned to a register class really is in one of that class's
    /// registers.
    #[test]
    fn checks_an_operands_register_class() {
        let other = RegClass::try_new(1).unwrap();
        let mut test_input = TestInput::with_two_uses_of_different_values();
        check_allocation(&test_input).unwrap();

        // The fixture's first read is pinned to `rc0`; ask the same
        // allocation for `rc1`, which holds the other register entirely.
        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, i, op)| i == 0 && op.kind() == DefUse::Use)
            .expect("the fixture reads two values in one instruction");

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, i) =
            Operand::new(op.pos(), op.kind(), OperandConstraint::Reg(other), op.val());

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("which is not in"), "{error}");
    }

    /// An instruction gets exactly one allocation per operand.
    #[test]
    fn checks_how_many_allocations_an_instruction_got() {
        let mut test_input = TestInput::with_two_uses_of_different_values();
        check_allocation(&test_input).unwrap();

        let (inst, _, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, i, op)| i == 0 && op.kind() == DefUse::Use)
            .expect("the fixture reads two values in one instruction");

        let allocated = test_input.clone();
        test_input.func.operands_mut(inst).push(op);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("allocation(s)"), "{error}");
    }

    /// An operand that must be in a register is not allowed to be on the
    /// stack.
    #[test]
    fn checks_that_a_register_operand_is_not_on_the_stack() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints(&[OperandConstraint::Stack]);
        check_allocation(&test_input).unwrap();

        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, _, op)| op.constraint() == OperandConstraint::Stack)
            .expect("the fixture constrains a use to the stack");

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, i) =
            Operand::new(op.pos(), op.kind(), OperandConstraint::Reg(class), op.val());

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("must be in a register"), "{error}");
    }

    /// A value that occupies a register group is placed in a group its class
    /// holds, and not just in any group.
    #[test]
    fn checks_a_group_operands_register_class() {
        let first = RegClass::try_new(usize::from(TestMachine::FIRST_GROUP_CLASS)).unwrap();
        let second = RegClass::try_new(usize::from(TestMachine::SECOND_GROUP_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints_in(
            TestMachine::groups_and_registers(),
            TestMachine::FIRST_GROUP_CLASS,
            OperandConstraint::Reg(first),
            &[OperandConstraint::Reg(first)],
        );
        check_allocation(&test_input).unwrap();

        // The value can only be in the first group, so demanding the second
        // one of the same allocation cannot be met.
        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, _, op)| op.kind() == DefUse::Use)
            .expect("the fixture has a use");

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, i) = Operand::new(
            op.pos(),
            op.kind(),
            OperandConstraint::Reg(second),
            op.val(),
        );

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("is allocated to group"), "{error}");
        assert!(error.contains("which is not in"), "{error}");
    }

    /// A value that occupies a whole register group is not given a single
    /// register, and the count of locations it was given is checked too.
    #[test]
    fn checks_that_a_group_value_was_given_a_group() {
        let wide = RegClass::try_new(usize::from(TestMachine::WIDE_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints_in(
            TestMachine::groups_and_registers(),
            TestMachine::WIDE_REGS_CLASS,
            OperandConstraint::Any,
            &[OperandConstraint::Reg(wide)],
        );
        check_allocation(&test_input).unwrap();

        // Say the value occupies a whole group after allocating it into a
        // single register.
        let allocated = test_input.clone();
        test_input
            .func
            .set_reg_class(first_val(&test_input), TestMachine::FIRST_GROUP_CLASS);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("does not live in one"), "{error}");
        assert!(error.contains("occupies 2 register(s)"), "{error}");
    }

    /// A value on the stack is in a slot the size of one of its registers.
    #[test]
    fn checks_a_spill_slots_size() {
        let mut test_input = TestInput::with_use_constraints_in(
            TestMachine::groups_and_registers(),
            TestMachine::WIDE_REGS_CLASS,
            OperandConstraint::Any,
            &[OperandConstraint::Stack],
        );
        check_allocation(&test_input).unwrap();

        // Move the value to the other bank, an eighth the width, after it has
        // been given a slot sized for this one.
        let allocated = test_input.clone();
        test_input
            .func
            .set_reg_class(first_val(&test_input), TestMachine::NARROW_REGS_CLASS);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("byte(s) rather than"), "{error}");
    }

    /// A rematerialized value is one the input says may be rematerialized.
    #[test]
    fn checks_that_a_rematerialized_value_may_be_rematerialized() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints(&[
            OperandConstraint::Stack,
            OperandConstraint::Reg(class),
        ]);
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.remats > 0, "the fixture should rematerialize");

        let allocated = test_input.clone();
        test_input.set_remat_costs(None);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("rematerialization cost"), "{error}");
    }

    /// A parameter filled by rematerializing its argument is still the
    /// parameter: the remat names the argument, so the rename that follows it
    /// is what makes the register read as the parameter.
    #[test]
    fn a_rematerialized_block_argument_defines_the_parameter() {
        let test_input = TestInput::with_a_rematerialized_block_arg();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.remats > 0,
            "the fixture should rematerialize the argument"
        );
        assert!(
            stats.deferred_renames > 0,
            "the remat should be atop the block, ahead of the rename"
        );
    }

    /// A rematerialized value fits in one register, which is all a `Remat`
    /// names.
    #[test]
    fn checks_that_a_rematerialized_value_fits_in_one_register() {
        let wide = RegClass::try_new(usize::from(TestMachine::WIDE_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints_in(
            TestMachine::groups_and_registers(),
            TestMachine::WIDE_REGS_CLASS,
            OperandConstraint::Any,
            &[OperandConstraint::Stack, OperandConstraint::Reg(wide)],
        );
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.remats > 0, "the fixture should rematerialize");

        let allocated = test_input.clone();
        test_input
            .func
            .set_reg_class(first_val(&test_input), TestMachine::FIRST_GROUP_CLASS);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("occupies more than one register"), "{error}");
    }

    /// A tie is a register constraint too: the definition lands in a register
    /// of its own class, not merely wherever the operand it reuses went.
    /// `reuse_aware_constraint` strengthens both halves to `Reg(class)` before
    /// the allocator sees them, and the checker's class check is all that
    /// keeps that invariant from being taken on faith.
    #[test]
    fn checks_a_reuse_definitions_register_class() {
        let r0 = RegClass::try_new(0).unwrap();
        let mut test_input = TestInput::with_reuse_def(OperandConstraint::Reg(r0));
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.reuse_operands > 0, "the fixture should have a tie");

        // The tie pins both halves to `rc0`'s one register. Say the defined
        // value belongs to `rc1`, which holds only the other register.
        let (_, _, reuse) = operands(&test_input)
            .into_iter()
            .find(|&(_, _, op)| matches!(op.constraint(), OperandConstraint::Reuse(_)))
            .expect("the fixture has a tie");

        let allocated = test_input.clone();
        test_input.func.set_reg_class(reuse.val().unwrap(), 1);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("which is not in"), "{error}");
    }

    /// A tie is satisfied in a register and never on the stack.
    #[test]
    fn checks_that_a_reuse_is_not_satisfied_on_the_stack() {
        let mut test_input = TestInput::with_use_constraints(&[OperandConstraint::Stack]);
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.stack_operands > 0,
            "the fixture should put an operand on the stack",
        );

        // Declare the stack-allocated operand a reuse of itself. The validator
        // forbids that, but `check_against` does not validate the checked
        // copy, and it makes this a test of the register requirement alone:
        // the allocations trivially agree, so only `NotAReg` is left.
        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, _, op)| op.constraint() == OperandConstraint::Stack)
            .expect("the fixture constrains an operand to the stack");

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, i) =
            Operand::new(op.pos(), op.kind(), OperandConstraint::Reuse(i), op.val());

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("must be in a register"), "{error}");
    }

    /// An edit placed on a critical edge is on the edge it says it is on.
    #[test]
    fn checks_which_edge_a_critical_edge_edit_is_on() {
        let mut test_input = TestInput::with_a_critical_edge();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.critical_edge_edits > 0,
            "the fixture should put an edit on a critical edge",
        );

        // The critical edge is `block0`'s second successor. Point it
        // elsewhere, so the edit names an edge the function no longer has.
        let branch = test_input.with_input(|input| {
            input
                .func
                .block(Block::try_new(0).unwrap())
                .insts()
                .last()
                .expect("block0 has a terminator")
                .0
        });

        let allocated = test_input.clone();
        test_input
            .func
            .set_block_call_target(branch, 1, Block::try_new(1).unwrap());

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("which is not where it goes"), "{error}");
    }

    /// Break the edits a correct allocation generated, and check what is left.
    ///
    /// The tests above perturb the *function*, reaching everything the checker
    /// says about an operand but nothing about the code inserted between
    /// operands. This reaches the other half: run the pipeline by hand, reach
    /// into its edits, and build an `Output` over the result.
    ///
    /// The block is expanded once per entity representation, since
    /// `run_dispatch` picks the narrowest the input fits in and all three are
    /// enabled here.
    ///
    /// `block_point_edits` and `block_edge_edits` binary-search by position, so
    /// a perturbation may rewrite or drop an edit but not reorder one or
    /// change a position.
    macro_rules! check_with_broken_results {
        ($test_input:expr, |$inner:ident| $perturb:block) => {{
            let test_input: &TestInput = $test_input;
            let mut context = Context::new();

            let result = test_input.with_input(|input| -> Result<(), String> {
                crate::run_dispatch(&mut context, input)
                    .map_err(|e| format!("allocation failed: {e:?}"))?;

                match context.which.expect("`run_dispatch` chose a context") {
                    #[cfg(feature = "entity-repr-8")]
                    WhichContext::Context8 => {
                        let $inner = &mut context.context8;
                        $perturb
                    }
                    #[cfg(feature = "entity-repr-16")]
                    WhichContext::Context16 => {
                        let $inner = &mut context.context16;
                        $perturb
                    }
                    WhichContext::Context32 => {
                        let $inner = &mut context.context32;
                        $perturb
                    }
                }

                let output = Output::new(&context);
                let mut checker = Checker::new(input, &output);
                checker.analyze();
                checker.find_errors();
                checker.finish().map_err(|e| format!("{e:?}"))
            });

            context.reset();
            assert!(context.is_reset());
            result
        }};
    }

    /// `check_with_broken_results!` for the common case of breaking the edits.
    macro_rules! check_with_broken_edits {
        ($test_input:expr, |$edits:ident| $perturb:block) => {
            check_with_broken_results!($test_input, |inner| {
                let $edits = inner.move_generation.edits_mut();
                $perturb
            })
        };
    }

    /// A rematerialized value is one that is computed from nothing.
    ///
    /// A `Remat` carries no inputs, so it can only stand in for a definition
    /// that reads nothing --- which is the rule `index_remats` picks its
    /// candidates by --- and never for a block parameter, which no instruction
    /// computes at all.
    #[test]
    fn checks_that_a_rematerialized_value_is_computed_from_nothing() {
        // The parameter half: point the remat at the value the edge defines
        // rather than the argument it carries.
        let test_input = TestInput::with_a_rematerialized_block_arg();
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.remats > 0, "the fixture should rematerialize");

        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::Remat(remat) = edit {
                    // `v1` is the block parameter this fixture defines.
                    remat.val = Val::try_new(1).unwrap();
                }
            }
        })
        .unwrap_err();
        assert!(
            error.contains("is a block parameter and so no instruction computes"),
            "{error}",
        );

        // And the reading half: leave the remat where it is and give the
        // definition it stands in for an operand to read. That also leaves the
        // instruction with more operands than the results give it allocations,
        // which is reported as well; `check_against` does not validate the
        // copy it checks, and this is the only way to reach a definition that
        // reads from a fixture whose definitions do not.
        let mut test_input = TestInput::with_a_rematerialized_block_arg();
        let allocated = test_input.clone();
        let def = Inst::try_new(0).unwrap();
        let arg = first_val(&test_input);
        test_input.func.operands_mut(def).push(Operand::new(
            Position::Early,
            DefUse::Use,
            OperandConstraint::Any,
            Some(arg),
        ));

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("computes from values it reads"), "{error}",);
    }

    /// A value that the allocator moved from one place to another does not
    /// arrive if the move is taken away.
    #[test]
    fn checks_that_the_moves_between_two_operands_really_happen() {
        let test_input = TestInput::with_stack_param_and_arg();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.spills + stats.reloads + stats.reg_reg_moves > 0,
            "the fixture should move its value about",
        );

        let error = check_with_broken_edits!(&test_input, |edits| {
            edits.retain(|(_, edit)| !matches!(edit, Edit::Move(_)));
        })
        .unwrap_err();
        assert!(error.contains("reads register"), "{error}");
    }

    /// A block has exactly as many parameter allocations as it has parameters.
    ///
    /// The two are walked together, so a short list of allocations would
    /// otherwise decide how many parameters get checked at all, and the rest
    /// would go unexamined rather than unallocated.
    #[test]
    fn checks_the_number_of_block_param_allocations() {
        let mut test_input = TestInput::with_stack_param_and_arg();
        check_allocation(&test_input).unwrap();

        // The entry block is the one to grow: nothing branches to it, so the
        // extra parameter reaches the count check without first tripping the
        // renaming that an edge into a block would do.
        let allocated = test_input.clone();
        let entry = test_input.func.entry_block();
        let val = first_val(&test_input);
        test_input.func.push_block_param(entry, val);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("parameter(s) but was given"), "{error}");
    }

    /// A block parameter is where the results say it arrives.
    ///
    /// This gives the edge machinery teeth: a block's incoming moves are all
    /// that put a parameter in place, so a dropped one must be caught at the
    /// block's entry, not only wherever the parameter happens to be read.
    #[test]
    fn checks_that_a_block_param_arrives_where_the_results_say() {
        let test_input = TestInput::with_stack_param_and_arg();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.block_param_allocs > 0,
            "the fixture should give a block parameter a location",
        );

        // Only the edge can fill this parameter's slot, so taking the moves
        // away leaves it holding whatever was there before.
        let error = check_with_broken_edits!(&test_input, |edits| {
            edits.retain(|(_, edit)| !matches!(edit, Edit::Move(_)));
        })
        .unwrap_err();
        assert!(
            error.contains("according to the results, but is not there"),
            "{error}",
        );
    }

    /// Two of a block's parameters do not arrive in one location.
    ///
    /// The presence check above cannot say this: a location may legitimately
    /// hold several values at once. Exclusivity is its own question, and the
    /// answer is always no --- a caller cannot leave two arguments in one
    /// register, and elsewhere it is two interfering live-ins given the same.
    #[test]
    fn checks_that_two_block_params_do_not_share_a_location() {
        let test_input = TestInput::with_two_entry_params();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.block_param_allocs > 1,
            "the fixture should give both of its parameters a location",
        );

        // Report the second parameter as arriving where the first does. The
        // allocation is untouched, so this is purely a claim about the
        // contract --- one no caller could meet.
        let entry = Block::try_new(0).unwrap();
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            assert_eq!(params.len(), 2);
            params[1] = params[0];
        })
        .unwrap_err();
        assert!(error.contains("both arrive in"), "{error}");
    }

    /// A block parameter arrives somewhere its own value could legally live.
    ///
    /// Nothing else asks this. Every other legality check the checker makes is
    /// in `check_constraints`, which runs over instruction operands, and no
    /// operand ever names the arrival: the entry block's parameters are a
    /// contract with the caller, so an illegal one is a contract no caller
    /// could meet and no read would notice.
    ///
    /// One fixture for all four shapes, since only locations the results
    /// really mention can be claimed: inventing a spill slot would panic in
    /// `Output::spill_slot` before the check ran.
    #[test]
    fn checks_that_a_block_param_arrives_somewhere_it_could_live() {
        let test_input = TestInput::with_entry_params_in_two_banks();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.block_param_allocs > 2,
            "the fixture should give all three of its parameters a location",
        );

        let entry = Block::try_new(0).unwrap();

        // The group parameter, reported in a single slot: one location where
        // it occupies two registers, and not a group where it needs one.
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            params[0] = params[2];
        })
        .unwrap_err();
        assert!(error.contains("occupies 2 register(s)"), "{error}");
        assert!(
            error.contains("is a register group exactly when"),
            "{error}"
        );

        // The group parameter, reported in the machine's *other* group, which
        // is the right shape and the wrong class.
        let other_group = RegGroup::try_new(1).unwrap();
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            params[0] = Some(Allocation::Reg(RegAllocation::RegGroup(other_group)));
        })
        .unwrap_err();
        assert!(
            error.contains("is allocated to group1, which is not in rc0"),
            "{error}",
        );

        // The narrow parameter, reported in a register of the other bank.
        let wide_reg = Reg::try_new(0).unwrap();
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            params[2] = Some(Allocation::Reg(RegAllocation::Reg(wide_reg)));
        })
        .unwrap_err();
        assert!(
            error.contains("is allocated to r0, which is not in rc4"),
            "{error}",
        );

        // The narrow parameter, reported in the wide parameter's slot, which
        // is eight times the size one of its registers needs.
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            params[2] = params[1];
        })
        .unwrap_err();
        assert!(error.contains("rather than the 1 byte(s)"), "{error}");
    }

    /// A move or rematerialization placed after a block's terminator is only
    /// where the machine will run it when the terminator is the whole of the
    /// block's outgoing edge.
    ///
    /// Nothing else asks this: such an edit is applied to the block's state
    /// like any other, and the state cannot tell that the machine jumped away
    /// before reaching it.
    #[test]
    fn checks_that_an_edit_after_a_terminator_is_on_an_edge_it_may_be_on() {
        let mut test_input = TestInput::with_a_move_after_an_unconditional_branch();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.edits_after_terminator > 0,
            "the fixture should place an edit after one of its unconditional branches",
        );

        // Give the branch that hosts the edit a second outgoing edge, going
        // to the same place with the same argument. Nothing about where the
        // machine goes changes, but the block no longer leaves along the one
        // edge, so the code after its terminator is no longer that edge's.
        let allocated = test_input.clone();
        test_input
            .func
            .duplicate_block_call(Inst::try_new(4).unwrap(), 0);

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(
            error.contains("which is not an edge this edit may be placed on"),
            "{error}",
        );
    }

    /// An edit the allocator put on a critical edge names the edge it is
    /// really on, so a client splitting that edge splits the right one.
    #[test]
    fn checks_the_edge_a_critical_edge_edit_names() {
        let test_input = TestInput::with_a_critical_edge();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.critical_edge_edits > 0,
            "the fixture should put an edit on a critical edge",
        );

        // The critical edge is the predecessor's second outgoing edge.
        // Renumber the edit onto the first, which goes elsewhere, without
        // touching the position it is stored under.
        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::CriticalEdge(edit) = edit {
                    edit.succ = 0;
                }
            }
        })
        .unwrap_err();
        assert!(error.contains("which is not where it goes"), "{error}");
    }

    /// A rematerialization puts its value in a register of that value's own
    /// class --- a stronger claim than a move's destination can make, since a
    /// `Remat` names one value and no coalesced second one can disagree.
    #[test]
    fn checks_the_class_of_a_register_a_remat_targets() {
        let narrow = RegClass::try_new(usize::from(TestMachine::NARROW_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints_in(
            TestMachine::groups_and_registers(),
            TestMachine::NARROW_REGS_CLASS,
            OperandConstraint::Any,
            &[OperandConstraint::Stack, OperandConstraint::Reg(narrow)],
        );
        test_input.set_remat_costs(Some(RematCost::AlwaysRemat));
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.remats > 0, "the fixture should rematerialize");

        // The value lives in the narrow bank, so the machine's first register
        // -- a wide one -- is in no class it could ever occupy.
        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::Remat(remat) = edit {
                    remat.dest = Reg::try_new(0).unwrap();
                }
            }
        })
        .unwrap_err();
        assert!(error.contains("rematerializes"), "{error}");
        assert!(error.contains("which is not in"), "{error}");
    }

    /// A definition does not land in a register the machine never lets the
    /// allocator hand out.
    ///
    /// `check_reg_class` cannot say this. A non-allocatable register is in a
    /// class exactly when some operand needs to pin a read to it, and being in
    /// a class the value is allowed in is all that check asks for. But such a
    /// register covers no register units, so the allocator can see nothing
    /// interfere with a value that lives there and can keep nothing else off
    /// it: a definition there has no home at all.
    #[test]
    fn checks_that_a_definition_is_not_put_in_a_non_allocatable_register() {
        // An instruction's definition.
        let mut test_input = TestInput::with_a_move_after_an_unconditional_branch();
        let sp = test_input.machine.push_non_allocatable_reg(0);
        check_allocation(&test_input).unwrap();

        let def = Inst::try_new(0).unwrap();
        let error = check_with_broken_results!(&test_input, |inner| {
            let allocs = inner.output.inst_allocs_mut(def);
            assert_eq!(allocs.len(), 1);
            allocs[0] = Allocation::Reg(RegAllocation::Reg(sp));
        })
        .unwrap_err();
        assert!(
            error.contains(&format!(
                "operand 0 of inst0 is defined in {sp:?}, which is not allocatable"
            )),
            "{error}",
        );

        // And a block parameter, which is a definition of its own.
        let mut test_input = TestInput::with_two_entry_params();
        let sp = test_input.machine.push_non_allocatable_reg(0);
        check_allocation(&test_input).unwrap();

        let entry = Block::try_new(0).unwrap();
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            params[0] = Some(Allocation::Reg(RegAllocation::Reg(sp)));
        })
        .unwrap_err();
        assert!(
            error.contains(&format!("is defined in {sp:?}, which is not allocatable")),
            "{error}",
        );
    }

    /// A move into a register the allocator does not own carries something
    /// that was allowed to be there.
    ///
    /// Writing such a register is ordinary --- it is how a value reaches an
    /// operand pinned to `sp` --- so the question is never whether the move
    /// may happen but what it puts there: a value whose own class does not
    /// hold the register could not have been pinned to it by anything, and a
    /// source holding nothing the checker can name justifies nothing at all.
    #[test]
    fn checks_what_a_move_into_a_non_allocatable_register_carries() {
        let mut test_input = TestInput::with_a_move_after_an_unconditional_branch();
        let sp = test_input.machine.push_non_allocatable_reg(0);
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.reg_reg_moves > 0,
            "the fixture should move a value from one register to another",
        );

        // The moved value is in `rc2`, which holds the two registers the
        // allocator owns and not this one.
        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::Move(Move::RegReg { to, .. }) = edit {
                    *to = sp.with_repr().unwrap();
                }
            }
        })
        .unwrap_err();
        assert!(
            error.contains(&format!(
                "puts v0 in {sp:?}, which is not allocatable and not in v0's own register class"
            )),
            "{error}",
        );

        // Nothing ever writes this register, so a move out of it carries
        // nothing that could justify writing it back.
        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::Move(Move::RegReg { from, to }) = edit {
                    *from = sp.with_repr().unwrap();
                    *to = sp.with_repr().unwrap();
                }
            }
        })
        .unwrap_err();
        assert!(
            error.contains(&format!(
                "puts an unknown value in {sp:?}, which is not allocatable"
            )),
            "{error}",
        );
    }

    /// A move puts its value in a spill slot of the size that value needs, and
    /// not in one of some other value's.
    #[test]
    fn checks_the_size_of_a_slot_a_move_targets() {
        let test_input = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.spills > 0, "the fixture should spill both its values");

        // The fixture spills one value of each bank, so the two slots are the
        // machine's two sizes. Swapping them puts each value in a slot of
        // exactly the wrong size, and moves no edit off its position.
        let error = check_with_broken_edits!(&test_input, |edits| {
            let mut spills = edits
                .iter_mut()
                .filter_map(|(_, edit)| match edit {
                    Edit::Move(Move::Spill { to, .. }) => Some(to),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(spills.len(), 2, "the fixture should spill twice");
            let (first, rest) = spills.split_at_mut(1);
            core::mem::swap(first[0], rest[0]);
        })
        .unwrap_err();
        assert!(
            error.contains("byte(s) one of its registers needs"),
            "{error}"
        );
    }

    /// A slot the results move a value into is a slot the results allocate.
    ///
    /// Reading a slot's size is the first thing every stack check does, so
    /// without this the checker would panic on results that name a slot out of
    /// thin air rather than reporting them.
    #[test]
    fn checks_that_a_slot_the_results_use_is_one_they_allocate() {
        let test_input = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        let stats = check_allocation(&test_input).unwrap();
        assert!(stats.spills > 0, "the fixture should spill both its values");

        // Far past the two slots the fixture allocates, and still inside every
        // entity representation `run_dispatch` might have picked.
        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::Move(Move::Spill { to, .. }) = edit {
                    *to = SpillSlot::try_new(50).unwrap();
                }
            }
        })
        .unwrap_err();
        assert!(error.contains("which they do not allocate"), "{error}");
    }

    /// The edits atop a block are the ones its incoming edge delivers, so a
    /// critical-edge edit --- which goes on an edge the client has yet to
    /// split, and which the block's own stream keeps until the very end --- is
    /// never one of them.
    #[test]
    fn checks_that_no_critical_edge_edit_sits_atop_a_block() {
        let test_input = TestInput::with_a_rematerialized_block_arg();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.deferred_renames > 0,
            "the fixture should put a remat atop a block",
        );

        // Wrap the remat up as an edge edit without moving it off the position
        // it is stored under, which is a point atop the block.
        let error = check_with_broken_edits!(&test_input, |edits| {
            for (_, edit) in edits.iter_mut() {
                if let Edit::Remat(remat) = *edit {
                    *edit = Edit::CriticalEdge(CriticalEdgeEdit {
                        target: Block::try_new(1).unwrap(),
                        succ: 0,
                        edit: EdgeEdit::Remat(remat),
                    });
                }
            }
        })
        .unwrap_err();
        assert!(error.contains("sits among the edits atop"), "{error}");
    }

    /// A block's critical-edge edits are the last thing its stream holds:
    /// everything the block itself runs has already happened by the time an
    /// edge leaving it is reached.
    #[test]
    fn checks_that_nothing_follows_a_blocks_critical_edge_edits() {
        let test_input = TestInput::with_a_critical_edge();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.critical_edge_edits > 0,
            "the fixture should put an edit on a critical edge",
        );

        // Give the edge edit a neighbour stored under its own position, which
        // is the only way to put something after it: the positions themselves
        // are what sort the edge edits to the end.
        let error = check_with_broken_edits!(&test_input, |edits| {
            let i = edits
                .iter()
                .position(|(_, edit)| matches!(edit, Edit::CriticalEdge(_)))
                .expect("the fixture has a critical-edge edit");
            let pos = edits[i].0;
            let reg = Reg::try_new(0).unwrap();
            edits.insert(
                i + 1,
                (pos, Edit::Move(Move::RegReg { from: reg, to: reg })),
            );
        })
        .unwrap_err();
        assert!(
            error.contains("critical-edge edits, which are the last thing"),
            "{error}",
        );
    }

    /// A move's two registers are of one bank.
    ///
    /// A property of the move rather than of what it carries, so it is checked
    /// before the state is consulted: a move out of an unknown source carries
    /// no values, and a per-value check would then check nothing.
    #[test]
    fn checks_that_a_move_stays_within_one_bank() {
        let test_input = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        check_allocation(&test_input).unwrap();

        // One register from each of the machine's two banks.
        let (wide, narrow): (Reg, Reg) = (Reg::try_new(0).unwrap(), Reg::try_new(4).unwrap());
        test_input.with_input(|input| {
            assert_ne!(
                wide.bank(input.machine),
                narrow.bank(input.machine),
                "the fixture's machine should number its banks' registers this way",
            );
        });

        // Rewrite the first move as one that crosses the banks, leaving it at
        // the position it was stored under.
        let error = check_with_broken_edits!(&test_input, |edits| {
            let edit = edits
                .iter_mut()
                .find_map(|(_, edit)| matches!(edit, Edit::Move(_)).then_some(edit))
                .expect("the fixture should move its values about");
            *edit = Edit::Move(Move::RegReg {
                from: wide.with_repr().unwrap(),
                to: narrow.with_repr().unwrap(),
            });
        })
        .unwrap_err();
        assert!(error.contains("different banks"), "{error}");
        assert!(
            !error.contains("in a register of"),
            "the per-value check should have nothing to say about a move out of a \
             location the checker knows nothing about: {error}",
        );
    }

    /// A reload's slot is the size of the register it fills. Nothing else asks
    /// this: the per-value checks look only at where a move *writes*.
    #[test]
    fn checks_the_size_of_the_slot_a_move_reads() {
        let test_input = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.reloads > 0,
            "the fixture should reload both its values",
        );

        // The two reloads read the two sizes of slot the machine has, so
        // swapping their sources makes each of them read the wrong size.
        let error = check_with_broken_edits!(&test_input, |edits| {
            let mut reloads = edits
                .iter_mut()
                .filter_map(|(_, edit)| match edit {
                    Edit::Move(Move::Reload { from, .. }) => Some(from),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(reloads.len(), 2, "the fixture should reload twice");
            let (first, rest) = reloads.split_at_mut(1);
            core::mem::swap(first[0], rest[0]);
        })
        .unwrap_err();
        assert!(
            error.contains("byte(s) the register at its other end needs"),
            "{error}",
        );
    }

    /// A move puts its value in a register of the bank that value lives in,
    /// and not in one that cannot hold it.
    #[test]
    fn checks_the_bank_of_a_register_a_move_targets() {
        let test_input = TestInput::with_values_in_two_banks_spilled_and_reloaded();
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.reloads > 0,
            "the fixture should reload both its values",
        );

        // Same trick on the way back: the two reloads land in the two banks,
        // so swapping destinations sends each value to the wrong one.
        let error = check_with_broken_edits!(&test_input, |edits| {
            let mut reloads = edits
                .iter_mut()
                .filter_map(|(_, edit)| match edit {
                    Edit::Move(Move::Reload { to, .. }) => Some(to),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(reloads.len(), 2, "the fixture should reload twice");
            let (first, rest) = reloads.split_at_mut(1);
            core::mem::swap(first[0], rest[0]);
        })
        .unwrap_err();
        assert!(error.contains("in a register of"), "{error}");
    }

    /// An operand that has to be in a register really is in one, and one that
    /// has to be on the stack really is there.
    #[test]
    fn checks_where_an_operand_went() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]);
        check_allocation(&test_input).unwrap();

        // Demand the stack for the operand the allocation already put in a
        // register, and check the same allocation against that.
        let allocated = test_input.clone();
        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, _, op)| op.constraint() == OperandConstraint::Reg(class))
            .expect("the fixture constrains a use to a register class");
        *test_input.func.operand_mut(inst, i) =
            Operand::new(op.pos(), op.kind(), OperandConstraint::Stack, op.val());

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("must be on the stack"), "{error}");
    }

    /// An operand really reads the value it names, and not whatever happens to
    /// be lying around in its allocation.
    #[test]
    fn checks_what_an_operand_reads() {
        let mut test_input = TestInput::with_reuse_def(OperandConstraint::Any);
        check_allocation(&test_input).unwrap();

        let (inst, i, op) = operands(&test_input)
            .into_iter()
            .find(|&(_, _, op)| op.kind() == DefUse::Use)
            .expect("the fixture has a use");

        // Another value the operand could name without changing the shape of
        // its allocation, and which is therefore not the one that is there.
        let read = op.val().expect("the fixture's uses all name a value");
        let other = test_input.with_input(|input| {
            let class = input.func.value(read).reg_class();
            input
                .func
                .values()
                .find(|&(val, ref data)| val != read && data.reg_class() == class)
                .map(|(val, _)| val)
                .expect("the fixture has a second value of the same class")
        });

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, i) =
            Operand::new(op.pos(), op.kind(), op.constraint(), Some(other));

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("reads register"), "{error}");
    }

    /// Two definitions of one instruction do not land in the same place.
    #[test]
    fn checks_for_conflicting_defs() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_reuse_def(OperandConstraint::Any);
        check_allocation(&test_input).unwrap();

        // Make the reuse a plain register constraint and its former target a
        // second definition, so the allocation ties two definitions together.
        let (inst, def_i, def_op, reuse) = operands(&test_input)
            .into_iter()
            .find_map(|(inst, i, op)| match op.constraint() {
                OperandConstraint::Reuse(target) => Some((inst, i, op, target)),
                _ => None,
            })
            .expect("the fixture has a reuse");

        let allocated = test_input.clone();
        *test_input.func.operand_mut(inst, def_i) = Operand::new(
            def_op.pos(),
            def_op.kind(),
            OperandConstraint::Reg(class),
            def_op.val(),
        );
        let reused = *test_input.func.operand_mut(inst, reuse);
        *test_input.func.operand_mut(inst, reuse) = Operand::new(
            def_op.pos(),
            DefUse::Def,
            OperandConstraint::Reg(class),
            reused.val(),
        );

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("both define"), "{error}");
    }

    /// A definition of one instruction does not land on something the same
    /// instruction reads at the same point.
    ///
    /// [`CheckerError::ConflictingDef`] cannot say this --- it compares
    /// definitions with definitions --- and neither can the state: the read
    /// happens before the write in the checker just as it does in the machine,
    /// so the read finds the right value and only the *other* reader of that
    /// register, if any, would ever notice.
    #[test]
    fn checks_for_a_def_that_clobbers_a_use() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let mut test_input = TestInput::with_reuse_def(OperandConstraint::Any);
        check_allocation(&test_input).unwrap();

        let (inst, def_i, def_op, reuse) = operands(&test_input)
            .into_iter()
            .find_map(|(inst, i, op)| match op.constraint() {
                OperandConstraint::Reuse(target) => Some((inst, i, op, target)),
                _ => None,
            })
            .expect("the fixture has a reuse");

        let allocated = test_input.clone();

        // Untie the pair, and move the read the tie named to the definition's
        // own point. The allocation still puts both in one register, which is
        // exactly right for the tie it was made for and destroys the read here.
        *test_input.func.operand_mut(inst, def_i) = Operand::new(
            def_op.pos(),
            def_op.kind(),
            OperandConstraint::Reg(class),
            def_op.val(),
        );
        let reused = *test_input.func.operand_mut(inst, reuse);
        *test_input.func.operand_mut(inst, reuse) = Operand::new(
            def_op.pos(),
            DefUse::Use,
            OperandConstraint::Reg(class),
            reused.val(),
        );

        let error = check_against(&allocated, &test_input).unwrap_err();
        assert!(error.contains("reads at the same point"), "{error}");
    }

    /// A value occupying a whole register group is checked member by member,
    /// so that crossed members are caught --- the perturbation a checker
    /// tracking whole allocations rather than [`Part`]s would miss, the value
    /// being really in the group and only its members' order wrong.
    #[test]
    fn checks_a_register_group_member_by_member() {
        let group_class = RegClass::try_new(usize::from(TestMachine::GROUP_CLASS)).unwrap();
        let test_input = TestInput::with_group_use_constraints(&[
            OperandConstraint::Stack,
            OperandConstraint::Reg(group_class),
        ]);
        let stats = check_allocation(&test_input).unwrap();
        assert!(
            stats.reg_group_operands > 0,
            "the fixture should read its value as a group",
        );

        // The stack use really is a spill, so the group comes back member by
        // member. Swap where the two land: same value, same two registers,
        // halves the wrong way round. One bank and one size, so nothing about
        // the moves themselves is disturbed.
        let error = check_with_broken_edits!(&test_input, |edits| {
            let mut reloads = edits
                .iter_mut()
                .filter_map(|(_, edit)| match edit {
                    Edit::Move(Move::Reload { to, .. }) => Some(to),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(
                reloads.len(),
                2,
                "the fixture should reload the group member by member",
            );
            let (first, rest) = reloads.split_at_mut(1);
            core::mem::swap(first[0], rest[0]);
        })
        .unwrap_err();
        assert!(error.contains("reads register 1 of"), "{error}");
    }

    /// The entry block's parameters are seeded from the results.
    ///
    /// Nothing in the function puts them anywhere:
    /// [`crate::Output::block_param_allocs`] is the contract the caller meets,
    /// `seed_entry` starts from it, and `check_block_params` holds the entry
    /// block to the same claim so a back edge cannot quietly disagree.
    #[test]
    fn function_parameters_are_seeded_from_the_results() {
        // A parameter of the *entry* block, which is what `seed_entry` is
        // about, read both in a register and off the stack so that the seed is
        // not merely the register the first read wanted anyway.
        let test_input = TestInput::with_an_entry_param_read_two_ways();
        let entry = Block::try_new(0).unwrap();

        // With no seed there is nothing for the first read to find, so this
        // alone fails if `seed_entry` stops seeding.
        check_allocation(&test_input).unwrap();

        let reported = test_input.with_input(|input| {
            let mut context = Context::new();
            crate::run_dispatch(&mut context, input).unwrap();
            let output = Output::new(&context);
            assert!(
                input.func.block(entry).params().next().is_some(),
                "the fixture's entry block should take a parameter",
            );
            let reported = output.block_param_allocs(entry).to_vec();
            assert!(
                reported.iter().all(|alloc| alloc.is_some()),
                "every entry parameter should have a reported arrival: {reported:?}",
            );
            reported
        });

        // Move the arrival. The seed moves with it, so presence still passes;
        // what fails is everything that reads the parameter, since the edits
        // still name where the allocator really put it.
        let narrow = RegClass::try_new(TestMachine::NARROW_REGS_CLASS.into()).unwrap();
        let elsewhere = test_input.with_input(|input| {
            narrow
                .member_set(input.machine)
                .iter()
                .find(|&reg| Some(Allocation::Reg(RegAllocation::Reg(reg))) != reported[0])
                .expect("the narrow class has a second register to move the parameter to")
        });
        let error = check_with_broken_results!(&test_input, |inner| {
            let params = inner.output.block_param_allocs_mut(entry);
            params[0] = Some(Allocation::Reg(RegAllocation::Reg(elsewhere)));
        })
        .unwrap_err();
        assert!(error.contains("reads register"), "{error}");
    }

    /// A definition tied to a read is put where that read is, even when the
    /// read's own operand says nothing and a sibling operand reading the same
    /// value is what pins it down.
    #[test]
    fn a_reuse_lands_where_its_target_is_actually_read() {
        let test_input = TestInput::with_a_reuse_of_a_pinned_read();
        check_allocation(&test_input).unwrap();
    }

    /// An operand that names a register the allocator does not own, and no
    /// value, checks out --- and reports that register back, which is what a
    /// client reads the operand's allocation for.
    #[test]
    fn a_val_less_read_reports_the_register_it_names() {
        let test_input = TestInput::with_a_val_less_read_of_a_non_allocatable_reg();
        check_allocation(&test_input).unwrap();

        let inst = Inst::try_new(0).unwrap();
        let mut context = Context::new();
        test_input.with_input(|input| {
            let operand = input.func.inst(inst).operand(0);
            assert_eq!(operand.val(), None);
            let OperandConstraint::Reg(class) = operand.constraint() else {
                unreachable!("the fixture pins its val-less read to a class")
            };

            // `p`, the class's one member, and so the only place this operand
            // could possibly be said to live.
            let RegClassMembers::Regs(regs) = class.members(input.machine) else {
                unreachable!("the fixture's classes hold single registers")
            };
            assert_eq!(regs.len(), 1);

            let output = crate::run(&mut context, input).unwrap();
            assert_eq!(
                output.inst_allocs(inst)[0],
                Allocation::Reg(RegAllocation::Reg(regs[0])),
            );
        });
    }

    /// `Position` is what orders the reads and writes within an instruction,
    /// and the fixtures exercise both of its values.
    #[test]
    fn both_positions_are_exercised() {
        let class = RegClass::try_new(usize::from(TestMachine::BOTH_REGS_CLASS)).unwrap();
        let test_input = TestInput::with_use_constraints(&[OperandConstraint::Reg(class)]);
        let ops = operands(&test_input);
        assert!(ops.iter().any(|&(_, _, op)| op.pos() == Position::Early));
        assert!(ops.iter().any(|&(_, _, op)| op.pos() == Position::Late));
    }
}
