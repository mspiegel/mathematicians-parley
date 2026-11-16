//! The modules of `corpus/lean-bridges/`, as values: a file that names a
//! lemma or definition of one imports its module.

/// A module of `corpus/lean-bridges/`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BridgeModule {
    PowerTactics,
    Logarithms,
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
    ZF,
}

impl BridgeModule {
    /// Every module, in no order Lean reads.
    pub const ALL: [BridgeModule; 13] = [
        BridgeModule::PowerTactics,
        BridgeModule::Logarithms,
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
        BridgeModule::ZF,
    ];

    /// The module's name, as a file imports it and as its namespace
    /// `LeanBridges.<name>` is written.
    pub fn name(self) -> &'static str {
        match self {
            BridgeModule::PowerTactics => "PowerTactics",
            BridgeModule::Logarithms => "Logarithms",
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
            BridgeModule::ZF => "ZF",
        }
    }

    /// The module of that name; None where no bridge module has it. What a
    /// record's text names, `LeanBridges.Counting.choose`, is read by it.
    pub fn of_name(name: &str) -> Option<BridgeModule> {
        BridgeModule::ALL.into_iter().find(|m| m.name() == name)
    }
}
