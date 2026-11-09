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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/four-x-plus-six-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FourXPlusSixLimit.FourXPlusSixLimit

set_option maxHeartbeats 400000 in
theorem four_x_plus_six_limit (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = 4 * x + 6) :
    Filter.Tendsto f (nhdsWithin (-1) ((Set.univ : Set ℝ) \ {-1})) (nhds 2) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ -1 ∧ abs (x - -1) < δ → abs (f x - 2) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 4 > 0 := by parley_order
    -- 1.2. proof
    have s1_2 : ∀ x : ℝ, x ≠ -1 ∧ abs (x - -1) < ε / 4 → abs (f x - 2) < ε := by
      intro x
      intro hA2
      -- 1.2.1. instantiate x := x in H2
      have s1_2_1 : f x = 4 * x + 6 := by exact (hH2 x)
      -- 1.2.2. mun:abs-difference-lt c := −1, δ := ε/4, from A2
      have s1_2_2 : -1 - ε / 4 < x ∧ x < -1 + ε / 4 := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (-1 : ℝ)) (δ := ε / 4))).mp hA2.2
      -- 1.2.3. inequalities
      have s1_2_3 : 2 - ε < 4 * x + 6 := by parley_order
      -- 1.2.4. transitivity, from 1.2.3, 1.2.1
      have s1_2_4 : 2 - ε < f x := by parley_order
      -- 1.2.5. inequalities
      have s1_2_5 : 4 * x + 6 < 2 + ε := by parley_order
      -- 1.2.6. transitivity, from 1.2.1, 1.2.5
      have s1_2_6 : f x < 2 + ε := by parley_order
      -- 1.2.7. join 1.2.4, 1.2.6
      have s1_2_7 : 2 - ε < f x ∧ f x < 2 + ε := by parley_set_side
      -- 1.2.8. mun:abs-difference-lt x := f(x), c := 2, δ := ε, from 1.2.7
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (2 : ℝ)) (δ := ε))).mpr (by parley_set_side)
    -- 1.3. exhibit, from 1.1, 1.2
    exact ⟨ε / 4, ⟨s1_1, s1_2⟩⟩
  -- 2. def:limit-at D := ℝ, c := −1, L := 2, from 1
  have r62_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (-1 : ℝ)) (L := (2 : ℝ)))).mpr (by parley_set_side)

end Parley.Proofs.Hammack.FourXPlusSixLimit.FourXPlusSixLimit
