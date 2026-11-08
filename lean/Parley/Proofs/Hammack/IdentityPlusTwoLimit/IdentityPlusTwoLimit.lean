module

public import OrderTactics
public import RealTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/identity-plus-two-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.IdentityPlusTwoLimit.IdentityPlusTwoLimit

set_option maxHeartbeats 400000 in
theorem identity_plus_two_limit (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x + 2) :
    Filter.Tendsto f (nhdsWithin 0 ((Set.univ : Set ℝ) \ {0})) (nhds 2) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 0 ∧ abs x < δ → abs (f x - 2) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. proof
    have s1_1 : ∀ x : ℝ, x ≠ 0 ∧ abs x < ε → abs (f x - 2) < ε := by
      intro x
      intro hA2
      -- 1.1.1. instantiate x := x in H2
      have s1_1_1 : f x = x + 2 := by exact (hH2 x)
      -- 1.1.2. mun:abs-difference-lt c := 0, δ := ε, from A2
      have s1_1_2 : 0 - ε < x ∧ x < ε := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by simpa only [sub_zero] using hA2.2) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by simpa only [sub_zero] using hA2.2)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by simpa only [sub_zero] using hA2.2) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by simpa only [sub_zero] using hA2.2) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by simpa only [sub_zero] using hA2.2); parley_rat_of_real h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by simpa only [sub_zero] using hA2.2); parley_set_side)
      -- 1.1.3. inequalities
      have s1_1_3 : 2 - ε < x + 2 := by parley_order
      -- 1.1.4. transitivity, from 1.1.3, 1.1.1
      have s1_1_4 : 2 - ε < f x := by parley_order
      -- 1.1.5. inequalities
      have s1_1_5 : x + 2 < 2 + ε := by parley_order
      -- 1.1.6. transitivity, from 1.1.1, 1.1.5
      have s1_1_6 : f x < 2 + ε := by parley_order
      -- 1.1.7. join 1.1.4, 1.1.6
      have s1_1_7 : 2 - ε < f x ∧ f x < 2 + ε := by parley_set_side
      -- 1.1.8. mun:abs-difference-lt x := f(x), c := 2, δ := ε, from 1.1.7
      first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (2 : ℝ)) (δ := ε))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (2 : ℝ)) (δ := ε))).mpr (by parley_set_side); parley_set_side)
    -- 1.2. exhibit, from A1, 1.1
    exact ⟨ε, ⟨hA1, s1_1⟩⟩
  -- 2. def:limit-at D := ℝ, c := 0, L := 2, from 1
  have r55_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (0 : ℝ)) (L := (2 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (0 : ℝ)) (L := (2 : ℝ)))).mpr (by parley_set_side); parley_set_side)

end Parley.Proofs.Hammack.IdentityPlusTwoLimit.IdentityPlusTwoLimit
