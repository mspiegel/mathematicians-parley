module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/five-power-minus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FivePowerMinusOne.FivePowerMinusOne

theorem five_power_minus_one (n : ℤ) (hH1 : 0 ≤ n) :
    (3 : ℤ) ∣ (5 ^ (2 * n).toNat - 1 : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (3 : ℤ) ∣ (5 ^ (2 * m).toNat - 1 : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (5 ^ (2 * 0) - 1 : ℤ) = 3 * 0 := by parley_arith
      -- 1.2. def:divides d := 3, n := 5^(2·0) − 1, from 1.1
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (5 ^ (2 * 0) - 1 : ℤ)))).mpr ⟨(0 : ℤ), s1_1⟩
    | succ m hK hIH =>
      -- 1.3. algebra
      have s1_3 : 2 * (m + 1) = 2 * m + 2 := by parley_ring
      -- 1.4. calculation
      have s1_4 : (5 ^ (2 * (m + 1)).toNat : ℤ) = 5 ^ (2 * m).toNat * 5 ^ 2 := by
        calc (5 ^ (2 * (m + 1)).toNat : ℤ) = 5 ^ (2 * m + 2).toNat := by (have h := congrArg (fun t : ℤ => 5 ^ t.toNat) s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 5 ^ (2 * m).toNat * 5 ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side))
      -- 1.5. mun:divides-multiple e := 3, a := 5^(2m) − 1, x := 25, from IH
      have s1_5 : (3 : ℤ) ∣ ((5 ^ (2 * m).toNat - 1) * 25 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (5 ^ (2 * m).toNat - 1 : ℤ)) (x := (25 : ℤ)) hIH)
      -- 1.6. def:divides d := 3, n := 24
      have r37_1 : (24 : ℤ) = 3 * 8 := by parley_arith
      have s1_6 : (3 : ℤ) ∣ (24 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (24 : ℤ)))).mpr ⟨(8 : ℤ), r37_1⟩
      -- 1.7. mun:divides-sum d := 3, a := (5^(2m) − 1)·25, b := 24, from 1.5, 1.6
      have s1_7 : (3 : ℤ) ∣ ((5 ^ (2 * m).toNat - 1) * 25 + 24 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := ((5 ^ (2 * m).toNat - 1) * 25 : ℤ)) (b := (24 : ℤ)) s1_5 s1_6)
      -- 1.8. substitute
      have c1 : ((5 ^ (2 * m).toNat - 1) * 25 + 24 : ℤ) = 5 ^ (2 * (m + 1)).toNat - 1 := by linear_combination (norm := parley_norm) (-1) * s1_4
      have row1 : (3 : ℤ) ∣ (5 ^ (2 * (m + 1)).toNat - 1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (3 : ℤ) ∣ t)) c1 s1_7; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
  -- 2. instantiate m := n in line 1
  exact (s1 n hH1)

end Parley.Proofs.Hammack.FivePowerMinusOne.FivePowerMinusOne
