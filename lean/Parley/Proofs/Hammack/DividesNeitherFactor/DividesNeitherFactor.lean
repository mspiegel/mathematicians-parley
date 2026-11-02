module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/divides-neither-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesNeitherFactor.DividesNeitherFactor

theorem divides_neither_factor (x : ℤ) (y : ℤ) (z : ℤ) (hH4 : x ≠ 0) (hH5 : ¬ x ∣ y * z) :
    (¬ x ∣ y ∧ ¬ x ∣ z) := by
  -- 1. contradiction
  have s1 : ¬ x ∣ y := by
    by_contra hc_hS1
    have hS1 : x ∣ y := by parley_suppose hc_hS1
    -- 1.1. mun:divides-multiple e := x, a := y, x := z, from S1
    have s1_1 : x ∣ y * z := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) (by parley_side)); parley_side)
    -- 1.2. restate H5
    have s1_2 : ¬ x ∣ y * z := by parley_side
    all_goals parley_side
  -- 2. contradiction
  have s2 : ¬ x ∣ z := by
    by_contra hc_hS2
    have hS2 : x ∣ z := by parley_suppose hc_hS2
    -- 2.1. mun:divides-multiple e := x, a := z, x := y, from S2
    have s2_1 : x ∣ z * y := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) (by parley_side)); parley_side)
    -- 2.2. substitute
    have s2_2 : x ∣ y * z := by
      have c1 : z * y = y * z := by parley_ring
      have row1 : x ∣ y * z := by parley_subst_at c1 s2_1
      exact row1
    -- 2.3. restate H5
    have s2_3 : ¬ x ∣ y * z := by parley_side
    all_goals parley_side
  -- 3. join 1, 2
  have s3 : ¬ x ∣ y ∧ ¬ x ∣ z := by parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.DividesNeitherFactor.DividesNeitherFactor
