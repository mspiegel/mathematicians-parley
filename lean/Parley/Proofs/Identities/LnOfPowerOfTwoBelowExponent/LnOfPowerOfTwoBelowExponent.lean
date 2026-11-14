module

public import PowerTactics
public import Roots
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Logarithms
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/ln-of-power-of-two-below-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LnOfPowerOfTwoBelowExponent.LnOfPowerOfTwoBelowExponent

theorem ln_of_power_of_two_below_exponent (n : ℤ) (hH1 : 0 < n) :
    Real.log (2 ^ n.toNat : ℝ) < (n : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.log (2 : ℝ) < 1 := by
    have hf1 : (5 / 8 : ℝ) < Real.log (2 : ℝ) := by exact_mod_cast Roots.log_above (p := 2) (a := 5) (b := 8) (by norm_num) (by norm_num) (by norm_num)
    have hf2 : Real.log (2 : ℝ) < (1 / 1 : ℝ) := by exact_mod_cast Roots.log_below (p := 2) (a := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    linarith only [hf1, hf2]
  -- 2. inequalities, from H1
  have s2 : n > 0 := by linarith only [hH1]
  -- 3. calculation
  have r16_1 : (2 : ℤ) > 0 := by norm_num
  calc Real.log (2 ^ n.toNat : ℝ) = (n : ℝ) * Real.log (2 : ℝ) := by (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := n) (by norm_num)); simp only [parley_zpow_toNat (n := n) (h := le_of_lt (lt_of_le_of_lt (by norm_num) s2))] at h ⊢; exact_mod_cast h)
    _ < (n : ℝ) * 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.log (2 : ℝ)) (y := (1 : ℝ)) (c := (n : ℝ)) (by exact_mod_cast gt_iff_lt.mp s2))).mp s1
    _ = (n : ℝ) := by ring_nf

end Parley.Proofs.Identities.LnOfPowerOfTwoBelowExponent.LnOfPowerOfTwoBelowExponent
