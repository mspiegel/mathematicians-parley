module

public import Mathlib
public import Tactics

/-!
# Arithmetic, and a contradiction's `suppose` line

`parley_arith` decides a closed fact of numbers, and `parley_suppose h`
proves a contradiction block's `suppose` line from the denial `h`. A
generated file imports this module only when it calls one of them, and
`RealTactics` imports it for `parley_arith`.
-/

public section

/-- `parley_suppose h`, where `h` denies what a contradiction block claims:
proves the block's `suppose` line, which says the same as `h` in the words
the page chose. -/
macro "parley_suppose " h:ident : tactic =>
  `(tactic| first
    | (exact $h; done)
    | (exact Eq.symm $h; done)
    | (push_neg at $h:ident; exact $h; done)
    | (push_neg at $h:ident; linarith; done)
    | (simpa using $h; done)
    | (simp only [not_not] at $h:ident; exact $h; done)
    | (simp only [not_not, ne_eq] at $h:ident; exact Eq.symm $h; done)
    | (push_neg at $h:ident; exact Eq.symm $h; done)
    | (intro _; apply $h; simp_all; done))

/-- `arithmetic`: a closed fact of numbers, worked out, and that a fraction
which is no whole number is no member of ℕ or ℤ. -/
macro "parley_arith" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | (norm_num [LeanBridges.Counting.factorial, LeanBridges.Counting.choose, Nat.factorial]; done)
    -- A sum or a product of integers over a range of numerals, which Lean
    -- works out term by term.
    | (decide; done)
    -- The same in ℚ, a product of 365 − k over a quotient: the division
    -- cleared, the casts taken off, and the integers worked out.
    | (field_simp; norm_cast; done)
    | (rintro ⟨m, _, h⟩; field_simp at h; norm_cast at h; omega)
    | (rintro ⟨m, h⟩; field_simp at h; norm_cast at h; omega))

end
