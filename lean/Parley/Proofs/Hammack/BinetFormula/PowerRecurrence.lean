module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/binet-formula.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinetFormula.PowerRecurrence

theorem power_recurrence (x : ℝ) (hH2 : x ^ 2 = x + 1) (k : ℤ) (hH3 : 0 ≤ k) :
    x ^ (k + 1 + 1).toNat = x ^ (k + 1).toNat + x ^ k.toNat := by
  -- 1. mun:exponent-step a := x, m := k
  have s1 : x ^ (k + 1).toNat = x ^ k.toNat * x := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k) hH3)
  -- 2. mun:exponent-step a := x, m := k + 1
  have s2 : x ^ (k + 1 + 1).toNat = x ^ (k + 1).toNat * x := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1) (add_nonneg (hH3) (by norm_num)))
  -- 3. calculation
  calc x ^ (k + 1 + 1).toNat = x ^ k.toNat * x * x := by linear_combination (norm := parley_norm) (x) * s1 + s2
    _ = x ^ k.toNat * (x + 1) := by linear_combination (norm := parley_norm) (x ^ k.toNat) * hH2
    _ = x ^ (k + 1).toNat + x ^ k.toNat := by linear_combination (norm := parley_norm) (-1) * s1

end Parley.Proofs.Hammack.BinetFormula.PowerRecurrence
