//! Proof skeletons: the `.proof` files.

use std::fmt;
use std::sync::Arc;

use indexmap::{IndexMap, IndexSet};

use super::define::{define_parts, naming, DefineParts, Naming, Param, RuleText};
use super::lines::{read_lines, Line};
use super::records::{Record, RecordKind};
use super::skeleton::{
    self, cut_reason, is_justification, item_kind, Cite, Cited, Place, Slots, Source,
};
use super::values::Values;
use super::{cited_name, in_stdlib, module_of};
use crate::formula::page::Written;
use crate::outcome::{Built, Checked, Problem, Route};
use crate::text::{prefix, repr};

use self::chains::*;
pub use self::chains::{
    chain, chain_cited, chain_reasons, reason_as_step, requires_as_step, rows,
    substitute_rows, Chain, ChainLine, Row, RowReason, SubstituteRow, CHAIN_RELATIONS,
};
pub use self::parse::parse_proof;
use self::steps::*;
pub use self::steps::{
    fmt, DefineLine, Forbid, FunctionImport, Head, Hypothesis, Import, Intro,
    ItemImport, ItemKind, Justification, Kinded, Manipulation, Method, Names, Opener,
    PartBy, PartOpening, Range, Reason, Requires, Step, StepNo, StepPlace, ITEM_KINDS,
    METHODS,
};
use self::theorem::*;
pub use self::theorem::{
    cited_items, in_scope, outermost, read_visible, references, visible, written_text,
    FileScope, InScope, Reference, ScopeId, Theorem, Visible,
};

mod chains;
mod parse;
mod steps;
mod theorem;
