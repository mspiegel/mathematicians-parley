module

public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven

theorem sign_of_even (n : ℤ) (hH1 : 0 < n) (hH2 : Even n) :
    ((-1) ^ n.toNat : ℤ) = 1 := by
  -- 1. obtain k: def:even, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp hH2
  -- 2. inequalities, from H1
  have s2 : n ≥ 1 := by parley_order
  -- 3. substitute n = 2·k (line 1) into line 2
  have s3 : 2 * k ≥ 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t ≥ 1)) s1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. inequalities, from 3
  have s4 : 2 * k > 0 := by parley_order
  -- 5. inequalities
  have s5 : k > 0 := by parley_order
  -- 6. mun:pos-int-nat m := k, from 5
  have s6 : 0 < k := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s5)
  -- 7. thm:even-power-of-minus-one, from 6
  have s7 : ((-1) ^ (2 * k) : ℚ) = 1 := by (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); simp only [parley_zpow_toNat (n := 2 * k) (h := mul_nonneg (by norm_num) (le_of_lt s6))] at h ⊢; exact_mod_cast h)
  -- 8. substitute 2·k = n (line 1) into line 7
  parley_subst_at s1 s7

end Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven
