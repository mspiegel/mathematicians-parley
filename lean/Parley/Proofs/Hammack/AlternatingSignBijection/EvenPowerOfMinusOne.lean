module

public import AlgebraTactics
public import ArithTactics
public import Functions
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

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

theorem even_power_of_minus_one (k : ℤ) (hH1 : 0 ≤ k) :
    ((-1) ^ (2 * k).toNat : ℤ) = 1 := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → ((-1) ^ (2 * j).toNat : ℤ) = 1 := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      parley_arith
    | succ j hK1 hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * (j + 1) = 2 * j + 2 := by parley_ring
      -- 1.3. calculation
      calc ((-1) ^ (2 * (j + 1)).toNat : ℤ) = (-1) ^ (2 * j + 2).toNat := by (have h := congrArg (fun t : ℤ => (-1) ^ t.toNat) s1_2; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (-1) ^ (2 * j).toNat * (-1) ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side))
        _ = 1 * (-1) ^ 2 := by (have h := congrArg (fun t : ℤ => t * (-1) ^ 2) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 := by norm_num
  -- 2. instantiate j := k in line 1
  exact (s1 k (by parley_side))

end Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne
