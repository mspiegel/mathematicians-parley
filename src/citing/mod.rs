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
mod parts;
mod supply;

pub use asked::{asked, filled, Asked};
pub use conclude::{concludes, derives, obtained, obtains, taken, Taken};
pub use library::{conjuncts, readings, with_parts, Group, Library, Proved};
pub use parts::{
    bound_in, claimed_member, finished, function_values, implied_facts, Parts,
};
pub use supply::{names_of, search, supply, Sites, Ways};
