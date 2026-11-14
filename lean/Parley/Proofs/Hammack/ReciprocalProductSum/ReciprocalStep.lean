module

public import AlgebraTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from proofs/hammack/reciprocal-product-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep

theorem reciprocal_step (m : ℤ) (hH1 : 0 < m) :
    1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by
  -- 1. algebra
  have s1 : 1 / (m : ℚ) - 1 / ((m : ℚ) + 1) = 1 / ((m : ℚ) * ((m : ℚ) + 1)) := by parley_ring
  -- 2. calculation
  calc 1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / (m : ℚ) + (1 / (m : ℚ) - 1 / ((m : ℚ) + 1)) := congrArg (fun t : ℚ => 1 - 1 / (m : ℚ) + t) s1.symm
    _ = 1 - 1 / ((m : ℚ) + 1) := by parley_ring

end Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep
