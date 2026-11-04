module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters

theorem triple_from_parameters (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) (k : ℕ) (hH4 : 0 < k) (m : ℕ) (hH5 : 0 < m) (n : ℕ) (hH6 : 0 < n) (hH7 : (c : ℤ) = (k : ℤ) * ((m : ℤ) ^ 2 + (n : ℤ) ^ 2)) (hH8 : ({(a : ℤ), (b : ℤ)} : Set ℤ) = ({(k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2), 2 * (k : ℤ) * (m : ℤ) * (n : ℤ)} : Set ℤ)) :
    (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 := by
  -- 1. mun:pair-equal c := k(m² − n²), d := 2kmn, from H8
  have s1 : (a : ℤ) = (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2) ∧ (b : ℤ) = 2 * (k : ℤ) * (m : ℤ) * (n : ℤ) ∨ (a : ℤ) = 2 * (k : ℤ) * (m : ℤ) * (n : ℤ) ∧ (b : ℤ) = (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2) := by first | exact ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := (a : ℤ)) (b := (b : ℤ)) (c := (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) (d := 2 * (k : ℤ) * (m : ℤ) * (n : ℤ)))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_pair_equal (a := (a : ℤ)) (b := (b : ℤ)) (c := (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) (d := 2 * (k : ℤ) * (m : ℤ) * (n : ℤ)))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := (a : ℤ)) (b := (b : ℤ)) (c := (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) (d := 2 * (k : ℤ) * (m : ℤ) * (n : ℤ)))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := (a : ℤ)) (b := (b : ℤ)) (c := (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) (d := 2 * (k : ℤ) * (m : ℤ) * (n : ℤ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := (a : ℤ)) (b := (b : ℤ)) (c := (k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) (d := 2 * (k : ℤ) * (m : ℤ) * (n : ℤ)))).mp (by parley_set_side); parley_set_side)
  -- 2. cases, from 1
  have s2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. calculation
      have s2_1 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 := by
        calc (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = ((k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) ^ 2 + (b : ℤ) ^ 2 := by parley_subst hC1.1
          _ = ((k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) ^ 2 + (2 * (k : ℤ) * (m : ℤ) * (n : ℤ)) ^ 2 := by parley_subst hC1.2
          _ = ((k : ℤ) * ((m : ℤ) ^ 2 + (n : ℤ) ^ 2)) ^ 2 := by parley_ring
          _ = (c : ℤ) ^ 2 := by parley_subst hH7
      all_goals parley_set_side
    · skip
      -- 2.2. calculation
      have s2_2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 := by
        calc (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (2 * (k : ℤ) * (m : ℤ) * (n : ℤ)) ^ 2 + (b : ℤ) ^ 2 := by parley_subst hC2.1
          _ = (2 * (k : ℤ) * (m : ℤ) * (n : ℤ)) ^ 2 + ((k : ℤ) * ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) ^ 2 := by parley_subst hC2.2
          _ = ((k : ℤ) * ((m : ℤ) ^ 2 + (n : ℤ) ^ 2)) ^ 2 := by parley_ring
          _ = (c : ℤ) ^ 2 := by parley_subst hH7
      all_goals parley_set_side
  all_goals exact s2

end Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters
