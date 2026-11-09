module

public import Functions
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/divisor-of-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower

theorem divisor_of_power (K : ℤ) (M : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : K ∣ M) :
    K ∣ M ^ n.toNat := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℤ, 0 < m → K ∣ M ^ m.toNat := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. restate H4
      have s1_1 : K ∣ M ^ 1 := by parley_side
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_1
    | succ m hK hIH =>
      -- 1.2. mun:divides-multiple e := K, a := M^m, x := M, from IH
      have s1_2 : K ∣ M ^ m.toNat * M := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH)
      -- 1.3. substitute
      have c1 : M ^ m.toNat * M = M ^ (m + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)).symm
      have row1 : K ∣ M ^ (m + 1).toNat := by parley_subst_at c1 s1_2
      exact row1
  -- 2. instantiate m := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower
