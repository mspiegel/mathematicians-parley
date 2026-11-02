module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/notations/there-is-no.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.ThereIsNo.ThereAreNoIntegersWithEighteenAPlusSixBOne

theorem there_are_no_integers_with_eighteen_a_plus_six_b_one :
    ¬ (∃ a : ℤ, ∃ b : ℤ, 18 * a + 6 * b = 1) := by
  -- 1. contradiction
  have s1 : ¬ (∃ a : ℤ, ∃ b : ℤ, 18 * a + 6 * b = 1) := by
    by_contra hc_hS
    have hS : ∃ a : ℤ, ∃ b : ℤ, 18 * a + 6 * b = 1 := by parley_suppose hc_hS
    -- 1.1. obtain a, b from S
    obtain ⟨a, b, s1_1⟩ := hS
    -- 1.2. algebra, from 1.1
    have s1_2 : 1 = 2 * (9 * a + 3 * b) := by linear_combination (norm := parley_norm) (-1) * s1_1
    -- 1.3. def:even n := 1, from 1.2
    have s1_3 : Even (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨9 * a + 3 * b, by parley_side⟩
    -- 1.4. mun:not-both n := 1, from 1.3
    have s1_4 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side))
    -- 1.5. arithmetic
    have s1_5 : Odd (1 : ℤ) := by parley_arith
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Notations.ThereIsNo.ThereAreNoIntegersWithEighteenAPlusSixBOne
