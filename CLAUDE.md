# Working in this repository

## Errors

**An error may not be used as control flow.** A route that does not apply, a
lemma that does not fit, a pattern that does not match, a parse with no reading:
none of those is a failure. They are the ordinary course of a run where nothing
has gone wrong, and what they give back is a value.

Two types in `src/outcome.rs` carry the distinction, and their doc comments hold
the reasoning rather than this file.

- `Problem` means a defect somebody has to fix — the proof text says something
  wrong, or a database record does. It is the error of `Checked<T>`, which is
  `Result<T, Problem>`; it is passed up with `?`, and nothing carries on past it.
- `Route::Declined` means a route asked whether it applies and the answer was
  no. A route gives back `Checked<Route<T>>`, and a caller asks by matching on
  the `Route`, or with `take!` or `or_try`.

Matching on an `Err(Problem)` to try something else is accepting a proof with a
defect in it. If what you are reaching for is code that catches an error and
then tries another way, the thing you want is a `Route::Declined`. A decline
that is a defect where it arrives is made one by saying so, with
`Decline::into_problem`.

Do not say a route declined with `None` or an empty value. `Option` already
means "absent" across the elaborator, so one more meaning moves the double duty
rather than ends it; and `spell::seq` drops empty parts, so a decline arriving
there as an empty string would shorten a proof and say nothing whatever. A
`Route` is neither: it cannot be passed where a term or a proof is wanted, and
it is `#[must_use]`, so a caller who forgot to look does not compile.

The test is whether the error can happen on a run where nothing is wrong. If it
fires hundreds of times in a green build, it is branching and it is spelt wrong.

## The design documents

Read the one that governs a change before making it.

- `docs/SYNTAX.md`, `docs/GRAMMAR.md`: how a proof is written and read.
  Before writing or changing a proof, a notation, or an import.
- `docs/DATABASE.md`: records, kinds and the mundane mark.
  Before adding or changing a library record.
- `docs/ELABORATION.md`: what the elaborator does, renaming of bound
  letters included. Before changing the elaborator, or proposing a lemma
  or rule to close a gap it may already close.
- `docs/METHODS.md`: what each method expands to.
- `docs/READERS.md`: who the text is for, dull facts and mundane steps.
  Before deciding whether something is named or mundane.
- `docs/SELECTION.md` and `docs/pilot/`: which theorems come next and how
  each pilot was done. Before starting a theorem.
- `docs/GEOMETRY.md`, `docs/LINTER.md`: the geometry encoding and the linter.
