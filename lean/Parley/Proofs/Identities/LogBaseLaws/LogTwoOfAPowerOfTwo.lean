module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.LogTwoOfAPowerOfTwo

theorem log_two_of_a_power_of_two (n : ℤ) (hH1 : 0 < n) :
    Real.log (2 ^ n.toNat : ℝ) / Real.log (2 : ℝ) = (n : ℝ) := by
  -- 1. mun:ln-power x := 2
  have r13_1 : (2 : ℤ) > 0 := by parley_arith
  have s1 : Real.log (2 ^ n.toNat : ℝ) = (n : ℝ) * Real.log (2 : ℝ) := by (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by norm_num)); simp only [parley_zpow_toNat (n := n) (h := le_of_lt hH1)] at h ⊢; exact_mod_cast h)
  -- 2. calculation
  have r17_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  calc Real.log (2 ^ n.toNat : ℝ) / Real.log (2 : ℝ) = (n : ℝ) * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by (have h := congrArg (fun t : ℝ => t / Real.log (2 : ℝ)) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = (n : ℝ) := by parley_ring

end Parley.Proofs.Identities.LogBaseLaws.LogTwoOfAPowerOfTwo
