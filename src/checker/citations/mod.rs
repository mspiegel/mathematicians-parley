//! A citation supplies what the item asks, and claims what it concludes.

use std::cell::OnceCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::formulas::chain_links;
use super::library::{
    introduced, listed_seed, parts_in_scope, typed_in_scope, typed_seed, Known,
    SaidFrom, Search,
};
use super::record::{
    Cited, Condition, Exhibit, Facing, FirstAt, Guard, Instantiated, ItemLetter,
    Narrowed, ObtainedPart, Supplied, SuppliedBy, Unfolded,
};
use super::structure::letters_in_scope;
use super::Report;
use crate::citing::{
    asked, bound_in, claimed_member, codomain_reason, concludes, conjuncts, derives,
    filled, finished, function_values, identities_unsaid, implied_by, index_system,
    obtained, obtains, range_system, readings, said_once, said_otherwise, search,
    stood_for, substitution_unsaid, supply, taken, taken_ways, type_said_otherwise,
    with_parts, witnesses_unsaid, Bound, CodomainAsk, Concluded, Group, Introduced,
    Library, Parts, Sites, Supplying, Taken, Way, Ways,
};
use crate::corpus::proof::{chain_reasons, reason_as_step, Requires};
use crate::corpus::skeleton::Source;
use crate::corpus::{
    define_parts, DefineParts, FileScope, Head, Intro, Item, Method, Step, Theorem,
};
use crate::formula::page::{self, conjoined, Written};
use crate::formula::symbol::Symbol;
use crate::formula::{ByShape, Node, Sort};
use crate::matching::{
    alike, binding_sites, expand, match_tree, standard, substitute_apart, Binding,
    Context, FxIndexMap, FxIndexSet,
};
use crate::notations::{
    APPLICATION, APPLICATION_TO_TWO, BICONDITIONAL, CONDITIONAL, CONGRUENT_MOD,
    EQUALITY, FOR_ALL, FOR_ALL_PART, FOR_ALL_SETS, FUNCTION_ON, FUNCTION_TYPE,
    IMPLICATION, IN, INTEGER_RANGE, LOGICAL_NOT, MAP, MEMBERSHIP, NUMBER_SYSTEMS,
    NUMERAL, ORDER, PLUS, POWERSET, PROPERTY_OF, SUBSET, THERE_IS, THERE_IS_SOME,
    WITHOUT,
};
use crate::outcome::{Built, Declined, Route};
use crate::rules::{self, System};
use crate::sorts::{types_a_function, TYPING};

use self::cited_facts::*;
pub use self::cited_facts::{
    cited, cited_requires, obtained_there, requires_cited, restatements,
};
pub(super) use self::cited_facts::{define_facing, facing_of, fact_at, placed};
use self::defined::*;
pub use self::defined::{
    applied_domains, check_cited_domains, check_conclusion_domains,
    check_define_domains, check_defined_types, check_stated_domains, define_domains,
};
pub(super) use self::defined::{
    defined_functions, domains_unsaid, letters_bound, Defined,
};
use self::exhibits::*;
pub use self::exhibits::{
    check_exhibited, check_instance_claimed, check_instantiated, exhibit_values,
    instantiations,
};
use self::joins::*;
pub use self::joins::{
    check_function_types, check_joins, check_recursions_cited, check_subjects,
    join_places,
};
pub(super) use self::kinds::domains_asked;
use self::kinds::*;
pub use self::kinds::{check_kinds, check_requires};
pub(super) use self::repeated::membership_said_once;
pub use self::repeated::{check_from_lines, check_repeated, check_surplus};
pub use self::substitutes::{
    check_obtained, check_obtained_claims, check_substitutes, obtained_parts,
    row_substitutions, sentence_substitutions, substitute_cases, substitutions,
};
use self::suppliers::*;
pub use self::suppliers::{bound_there, check_conclusion, check_hypotheses, searched};

mod cited_facts;
mod defined;
mod exhibits;
mod joins;
mod kinds;
mod repeated;
mod substitutes;
mod suppliers;
