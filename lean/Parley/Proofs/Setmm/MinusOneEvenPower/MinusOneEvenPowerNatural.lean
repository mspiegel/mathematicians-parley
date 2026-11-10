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

/-! Written from proofs/setmm/minus-one-even-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural

theorem minus_one_even_power_natural (n : ℤ) (hH1 : 0 ≤ n) :
    ((-1) ^ (2 * n).toNat : ℤ) = 1 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → ((-1) ^ (2 * k).toNat : ℤ) = 1 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      parley_arith
    | succ k hK hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * (k + 1) = 2 * k + 1 + 1 := by parley_ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * k + 1).toNat : ℤ) = -1 := by
        calc ((-1) ^ (2 * k + 1).toNat : ℤ) = (-1) ^ (2 * k).toNat * -1 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side))
          _ = 1 * -1 := by (have h := congrArg (fun t : ℤ => t * -1) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = -1 := by norm_num
      -- 1.4. calculation
      calc ((-1) ^ (2 * (k + 1)).toNat : ℤ) = (-1) ^ (2 * k + 1 + 1).toNat := by (have h := congrArg (fun t : ℤ => (-1) ^ t.toNat) s1_2; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (-1) ^ (2 * k + 1).toNat * -1 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1) (by parley_side))
        _ = -1 * -1 := by (have h := congrArg (fun t : ℤ => t * -1) s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 := by norm_num
  -- 2. instantiate k := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural
