module

public import ArithTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/two-does-not-divide-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TwoDoesNotDivideOdd.TwoDoesNotDivideOdd

theorem two_does_not_divide_odd (A : ℤ) :
    ¬ (2 : ℤ) ∣ 2 * A + 1 := by
  set B : ℤ := 2 * A + 1 with hD1
  -- the theorem. contradiction
  have sThm : ¬ (2 : ℤ) ∣ B := by
    by_contra hc_hS
    have hS : (2 : ℤ) ∣ B := by parley_suppose hc_hS
    -- 1. obtain k: def:divides d := 2, n := B, from S
    obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := B))).mp (by parley_side)
    -- 2. algebra, from D1, 1
    have s2 : 2 * (k - A) = 1 := by
      try simp only [hD1] at *
      try push_cast at *
      linear_combination (norm := parley_norm) (-1) * s1
    -- 3. def:divides d := 2, n := 1, from 2
    have s3 : (2 : ℤ) ∣ (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨k - A, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨k - A, by parley_side⟩; parley_side)
    -- 4. mun:divides-one d := 2, from 3
    have s4 : (2 : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := 2) (by parley_side) (by parley_side)); parley_side)
    exact absurd s4 (by norm_num)
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.TwoDoesNotDivideOdd.TwoDoesNotDivideOdd
