//! The stages of the gate that read the corpus against a list of names:
//! the labels set.mm must have, the items something must cite, and the steps
//! `ELABORATION.md` must record.

pub mod assumed;
pub mod build;
pub mod labels;
pub mod tested;

/// Where a generated file goes: its name under `elaboration/`, with `.mm`.
pub fn path_of(name: &str) -> String {
    format!("elaboration/{name}.mm")
}
