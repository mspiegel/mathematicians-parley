module

public import AlgebraTactics
public import RealTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTenOfThousand

theorem log_ten_of_thousand :
    Real.log (1000 : ℝ) / Real.log (10 : ℝ) = 3 := by
  -- 1. substitute ln(1000) = 3·ln(10) (real arithmetic)
  have s1 : Real.log (1000 : ℝ) / Real.log (10 : ℝ) = 3 * Real.log (10 : ℝ) / Real.log (10 : ℝ) := by
    have e_real : Real.log (1000 : ℝ) = 3 * Real.log (10 : ℝ) := by parley_real
    exact congrArg (fun t : ℝ => t / Real.log (10 : ℝ)) e_real
  -- 2. calculation
  have r25_1 : Real.log (10 : ℝ) ≠ 0 := by parley_real
  calc Real.log (1000 : ℝ) / Real.log (10 : ℝ) = 3 * Real.log (10 : ℝ) / Real.log (10 : ℝ) := s1
    _ = 3 := by parley_ring

end Parley.Proofs.Identities.LogBaseClosed.LogTenOfThousand
