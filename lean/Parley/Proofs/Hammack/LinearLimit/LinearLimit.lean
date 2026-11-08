module

public import OrderTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
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

/-! Written from proofs/hammack/linear-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LinearLimit.LinearLimit

set_option maxHeartbeats 400000 in
theorem linear_limit (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = 8 * x - 3) :
    Filter.Tendsto f (nhdsWithin 5 ((Set.univ : Set ℝ) \ {5})) (nhds 37) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 5 ∧ abs (x - 5) < δ → abs (f x - 37) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 8 > 0 := by parley_order
    -- 1.2. proof
    have s1_2 : ∀ x : ℝ, x ≠ 5 ∧ abs (x - 5) < ε / 8 → abs (f x - 37) < ε := by
      intro x
      intro hA2
      -- 1.2.1. instantiate x := x in H2
      have s1_2_1 : f x = 8 * x - 3 := by exact (hH2 x)
      -- 1.2.2. mun:abs-difference-lt c := 5, δ := ε/8, from A2
      have s1_2_2 : 5 - ε / 8 < x ∧ x < 5 + ε / 8 := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (5 : ℝ)) (δ := ε / 8))).mp hA2.2
      -- 1.2.3. inequalities
      have s1_2_3 : 37 - ε < 8 * x - 3 := by parley_order
      -- 1.2.4. transitivity, from 1.2.3, 1.2.1
      have s1_2_4 : 37 - ε < f x := by parley_order
      -- 1.2.5. inequalities
      have s1_2_5 : 8 * x - 3 < 37 + ε := by parley_order
      -- 1.2.6. transitivity, from 1.2.1, 1.2.5
      have s1_2_6 : f x < 37 + ε := by parley_order
      -- 1.2.7. join 1.2.4, 1.2.6
      have s1_2_7 : 37 - ε < f x ∧ f x < 37 + ε := by parley_set_side
      -- 1.2.8. mun:abs-difference-lt x := f(x), c := 37, δ := ε, from 1.2.7
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (37 : ℝ)) (δ := ε))).mpr (by parley_set_side)
    -- 1.3. exhibit, from 1.1, 1.2
    exact ⟨ε / 8, ⟨s1_1, s1_2⟩⟩
  -- 2. def:limit-at D := ℝ, c := 5, L := 37, from 1
  have r62_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (5 : ℝ)) (L := (37 : ℝ)))).mpr (by parley_set_side)

end Parley.Proofs.Hammack.LinearLimit.LinearLimit
