module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.LogTwoOfAPowerOfTwo

theorem log_two_of_a_power_of_two (n : ℤ) (hH1 : 0 < n) :
    Real.log (2 ^ n.toNat : ℝ) / Real.log (2 : ℝ) = (n : ℝ) := by
  -- 1. mun:ln-power x := 2
  have r13_1 : (2 : ℤ) > 0 := by parley_arith
  have s1 : Real.log (2 ^ n.toNat : ℝ) = (n : ℝ) * Real.log (2 : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by parley_side)); parley_side)
  -- 2. calculation
  have r17_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s2 : Real.log (2 ^ n.toNat : ℝ) / Real.log (2 : ℝ) = (n : ℝ) := by
    calc Real.log (2 ^ n.toNat : ℝ) / Real.log (2 : ℝ) = (n : ℝ) * Real.log (2 : ℝ) / Real.log (2 : ℝ) := by parley_subst s1
      _ = (n : ℝ) := by parley_ring
  all_goals exact s2

end Parley.Proofs.Identities.LogBaseLaws.LogTwoOfAPowerOfTwo
