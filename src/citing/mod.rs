//! What a cited item asks a citation to supply, and whether a citation's
//! claim is what the item concludes.
//!
//! An item's statement is read as patterns (`Library`, one `Group` per `then`
//! group), and a citation's lines and claim as ground facts (`Parts`). The
//! search here matches the one against the other: the hypotheses supplied by
//! the facts (`supply`), and the claim taken from a reading of the
//! conclusion (`concludes`). Each tool reads the page its own way and hands
//! the nodes over; the checker and the elaborator ask the one question
//! here, so that they answer it alike.

mod asked;
mod conclude;
mod library;
mod once;
mod parts;
mod supply;

pub use asked::{asked, asks_of, filled, Asked};
pub use conclude::{
    concludes, derives, identities_unsaid, link_unsaid, not_numbers, obtained, obtains,
    substitution_unsaid, taken, taken_ways, Concluded, Taken,
};
pub use library::{conjuncts, readings, with_parts, Group, Library, Proved, Way};
pub use once::{
    a_number_said_once, closed_nonzero, index_system, introduction, log_taken,
    nonzero_by_parts, nonzero_said_once, range_system, reason, reason_within,
    root_taken, said_once, sum_said_once, within, Introduced, OnceAsk, OnceReason,
    Shape,
};
pub use parts::{
    at_a_member, bound_in, claimed_member, finished, function_values, implied_facts,
    part_said_otherwise, stood_for, type_said_otherwise, typed_seed, Bound, Parts,
};
pub use supply::{largest_search, names_of, search, set_within, supply, Sites, Ways};
