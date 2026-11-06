module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters

theorem triple_from_parameters (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (k : ℤ) (hH4 : 0 < k) (m : ℤ) (hH5 : 0 < m) (n : ℤ) (hH6 : 0 < n) (hH7 : c = k * (m ^ 2 + n ^ 2)) (hH8 : ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  -- 1. mun:pair-equal c := k(m² − n²), d := 2kmn, from H8
  have s1 : a = k * (m ^ 2 - n ^ 2) ∧ b = 2 * k * m * n ∨ a = 2 * k * m * n ∧ b = k * (m ^ 2 - n ^ 2) := by first | exact ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := a) (b := b) (c := k * (m ^ 2 - n ^ 2)) (d := 2 * k * m * n))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_pair_equal (a := a) (b := b) (c := k * (m ^ 2 - n ^ 2)) (d := 2 * k * m * n))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := a) (b := b) (c := k * (m ^ 2 - n ^ 2)) (d := 2 * k * m * n))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := a) (b := b) (c := k * (m ^ 2 - n ^ 2)) (d := 2 * k * m * n))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := a) (b := b) (c := k * (m ^ 2 - n ^ 2)) (d := 2 * k * m * n))).mp (by parley_set_side); parley_set_side)
  -- 2. cases, from 1
  have s2 : a ^ 2 + b ^ 2 = c ^ 2 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. calculation
      have s2_1 : a ^ 2 + b ^ 2 = c ^ 2 := by
        calc a ^ 2 + b ^ 2 = (k * (m ^ 2 - n ^ 2)) ^ 2 + b ^ 2 := by parley_subst hC1.1
          _ = (k * (m ^ 2 - n ^ 2)) ^ 2 + (2 * k * m * n) ^ 2 := by parley_subst hC1.2
          _ = (k * (m ^ 2 + n ^ 2)) ^ 2 := by parley_ring
          _ = c ^ 2 := by parley_subst hH7
      all_goals parley_set_side
    · skip
      -- 2.2. calculation
      have s2_2 : a ^ 2 + b ^ 2 = c ^ 2 := by
        calc a ^ 2 + b ^ 2 = (2 * k * m * n) ^ 2 + b ^ 2 := by parley_subst hC2.1
          _ = (2 * k * m * n) ^ 2 + (k * (m ^ 2 - n ^ 2)) ^ 2 := by parley_subst hC2.2
          _ = (k * (m ^ 2 + n ^ 2)) ^ 2 := by parley_ring
          _ = c ^ 2 := by parley_subst hH7
      all_goals parley_set_side
  all_goals exact s2

end Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters
