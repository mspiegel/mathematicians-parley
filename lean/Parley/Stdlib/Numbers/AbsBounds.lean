module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Numbers.AbsBounds

set_option maxHeartbeats 400000 in
theorem abs_bounds (x : ℝ) :
    x ≤ abs x ∧ -x ≤ abs x := by
  -- 1. mun:nonneg-or-neg
  have s1 : x ≥ 0 ∨ x < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x))
  -- 2. cases, from 1
  have s2a_all : x ≤ abs x ∧ -x ≤ abs x := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. def:abs, from C1
      have s2_1 : abs x = x := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) hC1
      -- 2.2. inequalities
      have s2_2 : x ≤ abs x := by parley_order
      -- 2.3. inequalities
      have s2_3 : -x ≤ 0 := by parley_order
      -- 2.4. transitivity, from 2.3, C1, 2.1
      have s2_4 : -x ≤ abs x := by parley_order
      -- 2.5. join 2.2, 2.4
      have s2_5a : x ≤ abs x := by parley_side
      have s2_5b : -x ≤ abs x := by parley_side
      exact ⟨s2_5a, s2_5b⟩
    · skip
      -- 2.6. def:abs, from C2
      have s2_6 : abs x = -x := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) hC2
      -- 2.7. inequalities
      have s2_7 : -x ≤ abs x := by parley_order
      -- 2.8. inequalities
      have s2_8 : 0 < -x := by parley_order
      -- 2.9. transitivity, from C2, 2.8, 2.6
      have s2_9 : x < abs x := by parley_order
      -- 2.10. inequalities
      have s2_10 : x ≤ abs x := by parley_order
      -- 2.11. join 2.7, 2.10
      have s2_11a : x ≤ abs x := by parley_side
      have s2_11b : -x ≤ abs x := by parley_side
      exact ⟨s2_11a, s2_11b⟩
  obtain ⟨s2a, s2b⟩ := s2a_all
  exact ⟨s2a, s2b⟩

end Parley.Stdlib.Numbers.AbsBounds
