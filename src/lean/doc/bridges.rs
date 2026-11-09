//! The modules of `corpus/lean-bridges/` and the tactics they define, as
//! values: a file that names one imports its module, and a name no bridge
//! defines cannot be written.

/// A module of `corpus/lean-bridges/`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BridgeModule {
    Tactics,
    NormTactics,
    SetTactics,
    AlgebraTactics,
    SubstTactics,
    OrderTactics,
    PowerTactics,
    InstanceTactics,
    ComplexTactics,
    ArithTactics,
    RealTactics,
    WholeTactics,
    FactorialTactics,
    Roots,
    Counting,
    Divisibility,
    Numbers,
    Functions,
    Sums,
    Calculus,
    Factorials,
    Polynomials,
    Sets,
    Groups,
}

impl BridgeModule {
    /// Every module, in no order Lean reads.
    pub const ALL: [BridgeModule; 24] = [
        BridgeModule::Tactics,
        BridgeModule::NormTactics,
        BridgeModule::SetTactics,
        BridgeModule::AlgebraTactics,
        BridgeModule::SubstTactics,
        BridgeModule::OrderTactics,
        BridgeModule::PowerTactics,
        BridgeModule::InstanceTactics,
        BridgeModule::ComplexTactics,
        BridgeModule::ArithTactics,
        BridgeModule::RealTactics,
        BridgeModule::WholeTactics,
        BridgeModule::FactorialTactics,
        BridgeModule::Roots,
        BridgeModule::Counting,
        BridgeModule::Divisibility,
        BridgeModule::Numbers,
        BridgeModule::Functions,
        BridgeModule::Sums,
        BridgeModule::Calculus,
        BridgeModule::Factorials,
        BridgeModule::Polynomials,
        BridgeModule::Sets,
        BridgeModule::Groups,
    ];

    /// The module's name, as a file imports it and as its namespace
    /// `LeanBridges.<name>` is written.
    pub fn name(self) -> &'static str {
        match self {
            BridgeModule::Tactics => "Tactics",
            BridgeModule::NormTactics => "NormTactics",
            BridgeModule::SetTactics => "SetTactics",
            BridgeModule::AlgebraTactics => "AlgebraTactics",
            BridgeModule::SubstTactics => "SubstTactics",
            BridgeModule::OrderTactics => "OrderTactics",
            BridgeModule::PowerTactics => "PowerTactics",
            BridgeModule::InstanceTactics => "InstanceTactics",
            BridgeModule::ComplexTactics => "ComplexTactics",
            BridgeModule::ArithTactics => "ArithTactics",
            BridgeModule::RealTactics => "RealTactics",
            BridgeModule::WholeTactics => "WholeTactics",
            BridgeModule::FactorialTactics => "FactorialTactics",
            BridgeModule::Roots => "Roots",
            BridgeModule::Counting => "Counting",
            BridgeModule::Divisibility => "Divisibility",
            BridgeModule::Numbers => "Numbers",
            BridgeModule::Functions => "Functions",
            BridgeModule::Sums => "Sums",
            BridgeModule::Calculus => "Calculus",
            BridgeModule::Factorials => "Factorials",
            BridgeModule::Polynomials => "Polynomials",
            BridgeModule::Sets => "Sets",
            BridgeModule::Groups => "Groups",
        }
    }

    /// The module of that name; None where no bridge module has it. What a
    /// record's text names, `LeanBridges.Counting.choose`, is read by it.
    pub fn of_name(name: &str) -> Option<BridgeModule> {
        BridgeModule::ALL.into_iter().find(|m| m.name() == name)
    }
}

/// A tactic the bridges define, or a lemma of theirs the writer names in a
/// tactic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BridgeTactic {
    Side,
    Norm,
    SetSide,
    CountAfter,
    CountExt,
    CountInt,
    EncardClosed,
    Finite,
    WitnessByOrder,
    Clear,
    Ring,
    Field,
    CastNe,
    NeZero,
    Nz,
    PosNe,
    Radical,
    Subst,
    SubstAt,
    PutAt,
    Order,
    IntPower,
    CastToNat,
    WitnessAt,
    WitnessNotAt,
    LineToNat,
    ZpowToNat,
    Instance,
    InstanceCast,
    InstanceReal,
    OfComplex,
    Arith,
    Suppose,
    Real,
    RatOfReal,
    WholeSide,
    Roots,
    RootsOrder,
    RootsSplit,
    RootFacts,
    Angles,
}

impl BridgeTactic {
    /// Every tactic, in no order Lean reads.
    pub const ALL: [BridgeTactic; 41] = [
        BridgeTactic::Side,
        BridgeTactic::Norm,
        BridgeTactic::SetSide,
        BridgeTactic::CountAfter,
        BridgeTactic::CountExt,
        BridgeTactic::CountInt,
        BridgeTactic::EncardClosed,
        BridgeTactic::Finite,
        BridgeTactic::WitnessByOrder,
        BridgeTactic::Clear,
        BridgeTactic::Ring,
        BridgeTactic::Field,
        BridgeTactic::CastNe,
        BridgeTactic::NeZero,
        BridgeTactic::Nz,
        BridgeTactic::PosNe,
        BridgeTactic::Radical,
        BridgeTactic::Subst,
        BridgeTactic::SubstAt,
        BridgeTactic::PutAt,
        BridgeTactic::Order,
        BridgeTactic::IntPower,
        BridgeTactic::CastToNat,
        BridgeTactic::WitnessAt,
        BridgeTactic::WitnessNotAt,
        BridgeTactic::LineToNat,
        BridgeTactic::ZpowToNat,
        BridgeTactic::Instance,
        BridgeTactic::InstanceCast,
        BridgeTactic::InstanceReal,
        BridgeTactic::OfComplex,
        BridgeTactic::Arith,
        BridgeTactic::Suppose,
        BridgeTactic::Real,
        BridgeTactic::RatOfReal,
        BridgeTactic::WholeSide,
        BridgeTactic::Roots,
        BridgeTactic::RootsOrder,
        BridgeTactic::RootsSplit,
        BridgeTactic::RootFacts,
        BridgeTactic::Angles,
    ];

    /// Its name in Lean.
    pub fn name(self) -> &'static str {
        match self {
            BridgeTactic::Side => "parley_side",
            BridgeTactic::Norm => "parley_norm",
            BridgeTactic::SetSide => "parley_set_side",
            BridgeTactic::CountAfter => "parley_count_after",
            BridgeTactic::CountExt => "parley_count_ext",
            BridgeTactic::CountInt => "parley_count_int",
            BridgeTactic::EncardClosed => "parley_encard_closed",
            BridgeTactic::Finite => "parley_finite",
            BridgeTactic::WitnessByOrder => "parley_witness_by_order",
            BridgeTactic::Clear => "parley_clear",
            BridgeTactic::Ring => "parley_ring",
            BridgeTactic::Field => "parley_field",
            BridgeTactic::CastNe => "parley_cast_ne",
            BridgeTactic::NeZero => "parley_ne_zero",
            BridgeTactic::Nz => "parley_nz",
            BridgeTactic::PosNe => "parley_pos_ne",
            BridgeTactic::Radical => "parley_radical",
            BridgeTactic::Subst => "parley_subst",
            BridgeTactic::SubstAt => "parley_subst_at",
            BridgeTactic::PutAt => "parley_put_at",
            BridgeTactic::Order => "parley_order",
            BridgeTactic::IntPower => "parley_int_power",
            BridgeTactic::CastToNat => "parley_cast_toNat",
            BridgeTactic::WitnessAt => "parley_witness_at",
            BridgeTactic::WitnessNotAt => "parley_witness_not_at",
            BridgeTactic::LineToNat => "parley_line_toNat",
            BridgeTactic::ZpowToNat => "parley_zpow_toNat",
            BridgeTactic::Instance => "parley_instance",
            BridgeTactic::InstanceCast => "parley_instance_cast",
            BridgeTactic::InstanceReal => "parley_instance_real",
            BridgeTactic::OfComplex => "parley_of_complex",
            BridgeTactic::Arith => "parley_arith",
            BridgeTactic::Suppose => "parley_suppose",
            BridgeTactic::Real => "parley_real",
            BridgeTactic::RatOfReal => "parley_rat_of_real",
            BridgeTactic::WholeSide => "parley_whole_side",
            BridgeTactic::Roots => "parley_roots",
            BridgeTactic::RootsOrder => "parley_roots_order",
            BridgeTactic::RootsSplit => "parley_roots_split",
            BridgeTactic::RootFacts => "parley_root_facts",
            BridgeTactic::Angles => "parley_angles",
        }
    }

    /// The module that defines it, which a file calling it imports.
    pub fn module(self) -> BridgeModule {
        match self {
            BridgeTactic::Side => BridgeModule::Tactics,
            BridgeTactic::Norm => BridgeModule::NormTactics,
            BridgeTactic::SetSide
            | BridgeTactic::CountAfter
            | BridgeTactic::CountExt
            | BridgeTactic::CountInt
            | BridgeTactic::EncardClosed
            | BridgeTactic::Finite
            | BridgeTactic::WitnessByOrder => BridgeModule::SetTactics,
            BridgeTactic::Clear
            | BridgeTactic::Ring
            | BridgeTactic::Field
            | BridgeTactic::CastNe
            | BridgeTactic::NeZero
            | BridgeTactic::Nz
            | BridgeTactic::PosNe
            | BridgeTactic::Radical => BridgeModule::AlgebraTactics,
            BridgeTactic::Subst | BridgeTactic::SubstAt | BridgeTactic::PutAt => {
                BridgeModule::SubstTactics
            }
            BridgeTactic::Order => BridgeModule::OrderTactics,
            BridgeTactic::IntPower
            | BridgeTactic::CastToNat
            | BridgeTactic::WitnessAt
            | BridgeTactic::WitnessNotAt
            | BridgeTactic::LineToNat
            | BridgeTactic::ZpowToNat => BridgeModule::PowerTactics,
            BridgeTactic::Instance
            | BridgeTactic::InstanceCast
            | BridgeTactic::InstanceReal => BridgeModule::InstanceTactics,
            BridgeTactic::OfComplex => BridgeModule::ComplexTactics,
            BridgeTactic::Arith | BridgeTactic::Suppose => BridgeModule::ArithTactics,
            BridgeTactic::Real | BridgeTactic::RatOfReal => BridgeModule::RealTactics,
            BridgeTactic::WholeSide => BridgeModule::WholeTactics,
            BridgeTactic::Roots
            | BridgeTactic::RootsOrder
            | BridgeTactic::RootsSplit
            | BridgeTactic::RootFacts
            | BridgeTactic::Angles => BridgeModule::Roots,
        }
    }
}
