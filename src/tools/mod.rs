//! The stages of the gate that read the corpus against a list of names:
//! the labels set.mm must have, the items something must cite, and the steps
//! `ELABORATION.md` must record.

pub mod assumed;
pub mod build;
pub mod gate;
pub mod labels;
pub mod restated;
pub mod tested;
pub mod verify;

/// Where the generated files go, under the working tree.
pub const ELABORATION: &str = "corpus/elaboration";

/// Where a generated file goes: its name under `corpus/elaboration/`, with
/// `.mm`, spelt in ASCII since a Metamath file includes it by that name.
pub fn path_of(name: &str) -> String {
    format!("{ELABORATION}/{}.mm", crate::text::spelt_in_ascii(name))
}
