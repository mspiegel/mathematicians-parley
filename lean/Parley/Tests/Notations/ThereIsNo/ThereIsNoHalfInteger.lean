module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/there-is-no.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.ThereIsNo.ThereIsNoHalfInteger

theorem there_is_no_half_integer :
    ¬ (∃ x : ℤ, 2 * x = 1) := by
  -- 1. contradiction
  have s1 : ¬ (∃ x : ℤ, 2 * x = 1) := by
    by_contra hc_hS
    have hS : ∃ x : ℤ, 2 * x = 1 := by parley_suppose hc_hS
    -- 1.1. obtain x from S
    obtain ⟨x, s1_1⟩ := hS
    -- 1.2. restate 1.1
    have s1_2 : 1 = 2 * x := by parley_side
    -- 1.3. def:even n := 1, from 1.2
    have s1_3 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨x, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨x, by parley_side⟩; parley_side)
    -- 1.4. mun:not-both n := 1, from 1.3
    have s1_4 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)); parley_side)
    -- 1.5. arithmetic
    have s1_5 : Odd (1 : ℤ) := by parley_arith
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Notations.ThereIsNo.ThereIsNoHalfInteger
