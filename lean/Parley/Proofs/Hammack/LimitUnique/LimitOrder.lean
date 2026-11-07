module

public import ArithTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.LimitUnique.LimitUnfolded

/-! Written from proofs/hammack/limit-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LimitUnique.LimitOrder

set_option maxHeartbeats 800000 in
theorem limit_order (f : ℝ → ℝ) (c : ℝ) (L : ℝ) (M : ℝ) (hH5 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L)) (hH6 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds M)) :
    M ≤ L := by
  -- the theorem. contradiction
  have sThm : M ≤ L := by
    by_contra hc_hS
    have hS : ¬ M ≤ L := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : L < M := by parley_order
    -- 2. inequalities
    have s2 : (M - L) / 3 > 0 := by parley_order
    -- 3. thm:limit-unfolded D := ℝ, from H5
    have r51_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
    have s3 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε)) := by first | exact (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := L) (by parley_whole_side)) | exact ((Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := L) (by parley_whole_side))).symm | simpa using (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := L) (by parley_whole_side)) | exact_mod_cast (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := L) (by parley_whole_side)) | (have h := (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := L) (by parley_whole_side)); parley_set_side)
    -- 4. thm:limit-unfolded D := ℝ, L := M, from H6
    have r55_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
    have s4 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - M) < ε)) := by first | exact (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := M) (by parley_whole_side)) | exact ((Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := M) (by parley_whole_side))).symm | simpa using (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := M) (by parley_whole_side)) | exact_mod_cast (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := M) (by parley_whole_side)) | (have h := (Parley.Proofs.Hammack.LimitUnique.LimitUnfolded.limit_unfolded (D := (Set.univ : Set ℝ)) (by parley_whole_side) (f := f) (by parley_whole_side) (c := c) (L := M) (by parley_whole_side)); parley_set_side)
    -- 5. instantiate ε := (M − L)/3 in line 3, from 2
    have s5 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < (M - L) / 3) := by first | exact (s3 ((M - L) / 3) (by parley_set_side)) | exact ((s3 ((M - L) / 3) (by parley_set_side))).symm | simpa using (s3 ((M - L) / 3) (by parley_set_side)) | exact_mod_cast (s3 ((M - L) / 3) (by parley_set_side)) | (have h := (s3 ((M - L) / 3) (by parley_set_side)); parley_set_side)
    -- 6. instantiate ε := (M − L)/3 in line 4, from 2
    have s6 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - M) < (M - L) / 3) := by first | exact (s4 ((M - L) / 3) (by parley_set_side)) | exact ((s4 ((M - L) / 3) (by parley_set_side))).symm | simpa using (s4 ((M - L) / 3) (by parley_set_side)) | exact_mod_cast (s4 ((M - L) / 3) (by parley_set_side)) | (have h := (s4 ((M - L) / 3) (by parley_set_side)); parley_set_side)
    -- 7. obtain p from line 5
    obtain ⟨p, ⟨s7a, s7b⟩⟩ := s5
    -- 8. obtain q from line 6
    obtain ⟨q, ⟨s8a, s8b⟩⟩ := s6
    set m : ℝ := min p q with hD1
    have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_min_real (x := p) (y := q)) | exact ((Parley.Items.Stdlib.Numbers.mun_min_real (x := p) (y := q))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_min_real (x := p) (y := q)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_min_real (x := p) (y := q)) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := p) (y := q)); parley_set_side)
    -- 9. mun:lt-min z := 0, x := p, y := q, from 7, 8
    have s9 : 0 < min p q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := p) (y := q))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := p) (y := q))).mpr (by parley_set_side); parley_set_side)
    -- 10. mun:min-le x := p, y := q
    have s10a : min p q ≤ p := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := p) (y := q))] | (have h := (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := p) (y := q)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := p) (y := q)) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := p) (y := q)); parley_set_side)
    have s10b : min p q ≤ q := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := p) (y := q))] | (have h := (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := p) (y := q)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := p) (y := q)) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := p) (y := q)); parley_set_side)
    set x₁ : ℝ := c + m / 2 with hD2
    have hD2_kind : True := by parley_set_side
    -- 11. inequalities, from D1, 9
    have s11 : 0 < m := by parley_order
    -- 12. inequalities
    have s12 : c < c + m / 2 := by parley_order
    -- 13. inequalities
    have s13 : c ≠ c + m / 2 := by parley_set_side
    -- 14. inequalities, from D2, 13
    have s14 : x₁ ≠ c := by parley_set_side
    -- 15. inequalities
    have s15 : c + m / 2 < c + m := by parley_order
    -- 16. inequalities, from D1, 10
    have s16 : m ≤ p := by parley_order
    -- 17. inequalities, from D1, 10
    have s17 : m ≤ q := by parley_order
    -- 18. inequalities
    have s18 : c + m ≤ c + p := by parley_order
    -- 19. inequalities
    have s19 : c + m ≤ c + q := by parley_order
    -- 20. transitivity, from 15, 18
    have s20 : c + m / 2 < c + p := by parley_order
    -- 21. transitivity, from 15, 19
    have s21 : c + m / 2 < c + q := by parley_order
    -- 22. inequalities
    have s22 : c - p < c := by parley_order
    -- 23. inequalities
    have s23 : c - q < c := by parley_order
    -- 24. transitivity, from 22, 12
    have s24 : c - p < c + m / 2 := by parley_order
    -- 25. transitivity, from 23, 12
    have s25 : c - q < c + m / 2 := by parley_order
    -- 26. inequalities, from D2, 20, 24
    have s26 : c - p < x₁ ∧ x₁ < c + p := by parley_set_side
    -- 27. inequalities, from D2, 21, 25
    have s27 : c - q < x₁ ∧ x₁ < c + q := by parley_set_side
    -- 28. mun:abs-difference-lt x := x₁, δ := p, from 26
    have s28 : abs (x₁ - c) < p := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x₁) (c := c) (δ := p))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x₁) (c := c) (δ := p))).mpr (by parley_set_side); parley_set_side)
    -- 29. mun:abs-difference-lt x := x₁, δ := q, from 27
    have s29 : abs (x₁ - c) < q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x₁) (c := c) (δ := q))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x₁) (c := c) (δ := q))).mpr (by parley_set_side); parley_set_side)
    -- 30. instantiate x := x₁ in line 7, from 14, 28
    have s30 : abs (f x₁ - L) < (M - L) / 3 := by first | linarith [(s7b x₁ (by parley_set_side))] | (have h := (s7b x₁ (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s7b x₁ (by parley_set_side)) | (have h := (s7b x₁ (by parley_set_side)); parley_set_side)
    -- 31. instantiate x := x₁ in line 8, from 14, 29
    have s31 : abs (f x₁ - M) < (M - L) / 3 := by first | linarith [(s8b x₁ (by parley_set_side))] | (have h := (s8b x₁ (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s8b x₁ (by parley_set_side)) | (have h := (s8b x₁ (by parley_set_side)); parley_set_side)
    -- 32. mun:abs-difference-lt x := f(x₁), c := L, δ := (M − L)/3, from 30
    have s32 : f x₁ < L + (M - L) / 3 := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := L) (δ := (M - L) / 3))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := L) (δ := (M - L) / 3))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := L) (δ := (M - L) / 3))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := L) (δ := (M - L) / 3))).mp (by parley_set_side)).2; parley_set_side)
    -- 33. mun:abs-difference-lt x := f(x₁), c := M, δ := (M − L)/3, from 31
    have s33 : M - (M - L) / 3 < f x₁ := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := M) (δ := (M - L) / 3))).mp (by parley_set_side)).1] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := M) (δ := (M - L) / 3))).mp (by parley_set_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := M) (δ := (M - L) / 3))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x₁) (c := M) (δ := (M - L) / 3))).mp (by parley_set_side)).1; parley_set_side)
    -- 34. transitivity, from 33, 32
    have s34 : M - (M - L) / 3 < L + (M - L) / 3 := by parley_order
    -- 35. inequalities
    have s35 : M ≤ L := by parley_order
    all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.LimitUnique.LimitOrder
