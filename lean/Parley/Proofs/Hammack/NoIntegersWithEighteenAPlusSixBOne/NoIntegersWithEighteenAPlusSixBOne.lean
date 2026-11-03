module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/no-integers-with-eighteen-a-plus-six-b-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NoIntegersWithEighteenAPlusSixBOne.NoIntegersWithEighteenAPlusSixBOne

theorem no_integers_with_eighteen_a_plus_six_b_one :
    ¬ (∃ a : ℤ, ∃ b : ℤ, 18 * a + 6 * b = 1) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ a : ℤ, ∃ b : ℤ, 18 * a + 6 * b = 1) := by
    by_contra hc_hS
    have hS : ∃ a : ℤ, ∃ b : ℤ, 18 * a + 6 * b = 1 := by parley_suppose hc_hS
    -- 1. obtain a, b from S
    obtain ⟨a, b, s1⟩ := hS
    -- 2. algebra, from 1
    have s2 : 1 = 2 * (9 * a + 3 * b) := by linear_combination (norm := parley_norm) (-1) * s1
    -- 3. def:even n := 1, from 2
    have s3 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨9 * a + 3 * b, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨9 * a + 3 * b, by parley_side⟩; parley_side)
    -- 4. mun:not-both n := 1, from 3
    have s4 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3); parley_side)
    -- 5. arithmetic
    have s5 : Odd (1 : ℤ) := by parley_arith
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.NoIntegersWithEighteenAPlusSixBOne.NoIntegersWithEighteenAPlusSixBOne
