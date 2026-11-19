//! What the formulas on the page say: that each reads, that their sorts
//! fit, and that the methods which relate formulas are given the shapes
//! they need.

use std::collections::BTreeSet;

use indexmap::IndexMap;

use super::library::{Known, SaidFrom, Stated};
use super::record::{
    Antisymmetric, Chain, ChainLink, CheckedTheorem, Contradicted, FirstAt, Negating,
    OrderFact, OrderPart, OrderRestated, OrderStep, Supposed, Supposition, Weakened,
};
use super::structure::{defined_below, introduced, letters_in_scope};
use super::Report;
use crate::citing::{
    claimed_member, implied_facts, link_unsaid, not_numbers, said_once, said_otherwise,
    Library, Parts,
};
use crate::corpus::proof::{
    chain, rows, substitute_rows, visible, ChainLine, RowReason,
};
use crate::corpus::{
    define_parts, DefineParts, FileScope, Head, Intro, Item, Justification, Method,
    Opener, Record, RecordKind, Recursion, Requires, RuleText, Source, Step, Theorem,
    Value, Values,
};
use crate::formula::notation_id::{NotationId, Spelling};
use crate::formula::page::{
    conjoined, disjoined, made, made_by_name, numeral, related, Sentence, Written,
};
use crate::formula::symbol::Symbol;
use crate::formula::{walk, Node, Sort, Sorts};
use crate::matching::{
    alike_top, free_names, identities_dropped, standard, substitute_apart_by, Binding,
    FxIndexSet, Meeting,
};
use crate::methods::field::{decide_closed, Verdict};
use crate::methods::terms::{term_of_node, term_of_node_reading, Targets};
use crate::methods::{
    algebra, inequalities, linear, membership as methods_membership, reals,
};
use crate::mm::kernel::{FloatLabels, Term};
use crate::notations::{
    APPLICATION, APPLICATION_TO_TWO, AT_LEAST, AT_MOST, BICONDITIONAL, BY_CASES,
    CONDITIONAL, CONJUNCTION, EQUALITY, EQUALS, EQUAL_CHAIN, FOR_ALL, FOR_ALL_SETS,
    GREATER, IMPLICATION, INTEGER_RANGE, LESS, LOGICAL_NOT, MEMBERSHIP, NUMBER_SYSTEMS,
    NUMERAL, ORDER, PLUS, PRODUCT, PRODUCT_OVER, REAL_POWER, SINGLETON, SUM, TIMES,
    UNION,
};
use crate::outcome::{Built, Checked, Declined, Problem};
use crate::rules::System;
use crate::sorts::infer::{self, Reader, Store};
use crate::sorts::introduction::{Form, Introduction};
use crate::sorts::{define_sorts, types_a_function, unlabel, written_tokens, Env};
use crate::targets::split_entries;

pub use self::clashes::{
    check_clashes, check_decided_words, check_formulas, check_item_clashes,
    check_real_decided_words, defined_words, operations, read_with_citations,
    real_functions, real_operations, DefinedWord,
};
pub(super) use self::clashes::{claim_parts, one_formula_parts, FormulaPart};
use self::closures::*;
pub(super) use self::closures::{
    arithmetic_worked, fact_placed, real_worked, RealWorked, Worked,
};
pub use self::closures::{
    check_chain_links, check_closed_arithmetic, check_closed_by_arithmetic,
    check_closed_by_real_arithmetic, check_define_citation, check_membership_claims,
    check_real_arithmetic_holds, check_recursions, define_cases, define_link_meetings,
    link_places, pairs_apart,
};
use self::ends::*;
pub(super) use self::ends::{
    block_owes, block_owes_read, last_of_part, Ends, Owed, Reading,
};
pub use self::ends::{
    chain_links, check_algebra_holds, check_arithmetic_holds, check_block_ends,
    check_cases_cited, check_chain_congruences, check_ends_numbered,
    check_place_systems, ended_meetings, ends_asking, ends_unnumbered, places_at, Link,
};
use self::letters::*;
pub use self::letters::{
    check_both_directions, check_claimed_cases, check_contradicting,
    check_contradiction, check_impossible, check_letters_introduced,
    check_statement_names, check_structure_parts, contradictions, suppositions,
};
pub(super) use self::relations::define_equation;
use self::relations::*;
pub use self::relations::{
    antisymmetries, calculation_meetings, check_calculation_claims, check_define_names,
    check_substitute_rows, check_transitivity, divided_by, finite_under, order_steps,
    transitivity_links,
};
use self::rows::*;
pub use self::rows::{
    check_antisymmetry, check_inequalities_holds, check_inequality_rows,
    check_inspection_holds, check_kind_methods, check_membership_holds,
    check_method_cites_used, check_requires_combined, check_requires_manipulations,
    commuted_by_lines, held_by_lines, inspected, members_shown, reasons_under_lets,
};

mod clashes;
mod closures;
mod ends;
mod letters;
mod relations;
mod rows;
