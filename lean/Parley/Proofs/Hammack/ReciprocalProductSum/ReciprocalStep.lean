module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/hammack/reciprocal-product-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep

theorem reciprocal_step (m : ℤ) (hH1 : 0 < m) :
    1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by
  -- 1. algebra
  have s1 : 1 / (m : ℚ) - 1 / ((m : ℚ) + 1) = 1 / ((m : ℚ) * ((m : ℚ) + 1)) := by parley_ring
  -- 2. calculation
  have s2 : 1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by
    calc 1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / (m : ℚ) + (1 / (m : ℚ) - 1 / ((m : ℚ) + 1)) := by parley_subst s1
      _ = 1 - 1 / ((m : ℚ) + 1) := by parley_ring
  all_goals exact s2

end Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep
