module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne

theorem odd_power_of_minus_one (k : ℤ) (hH1 : 0 ≤ k) :
    ((-1) ^ (2 * k + 1).toNat : ℤ) = -1 := by
  -- 1. thm:even-power-of-minus-one
  have s1 : ((-1) ^ (2 * k).toNat : ℤ) = 1 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side))
  -- 2. calculation
  calc ((-1) ^ (2 * k + 1).toNat : ℤ) = (-1) ^ (2 * k).toNat * -1 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side))
    _ = 1 * -1 := by (have h := congrArg (fun t : ℤ => t * -1) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = -1 := by norm_num

end Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne
