module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-proof-block-ending-impossible.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProofBlockEndingImpossible.NothingBelowOneIsTwo

theorem nothing_below_one_is_two :
    (∀ x : ℝ, x ≤ 1 ∧ x = 2 → x = 5) := by
  -- 1. proof
  intro x
  intro hK2
  -- 1.1. restate K2
  have s1_1 : x ≤ 1 := by exact hK2.1
  -- 1.2. substitute x = 2 (K2) into line 1.1
  have s1_2 : (2 : ℝ) ≤ 1 := by (have h := Eq.subst (motive := (fun t : ℝ => t ≤ 1)) hK2.2 s1_1; revert h; norm_num)
  exact absurd s1_2 (by norm_num)

end Parley.Tests.Elaborator.AProofBlockEndingImpossible.NothingBelowOneIsTwo
