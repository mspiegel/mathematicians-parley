module

public import InstanceTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
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
public import Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd

theorem sign_of_odd (n : ℤ) (hH1 : 0 < n) (hH2 : Odd n) :
    ((-1) ^ n.toNat : ℤ) = -1 := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hH2
  -- 2. inequalities, from H1
  have s2 : n ≥ 1 := by parley_order
  -- 3. substitute n = 2·k + 1 (line 1) into line 2
  have s3 : 2 * k + 1 ≥ 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t ≥ 1)) s1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. inequalities
  have s4 : k ≥ 0 := by parley_order
  -- 5. mun:nat0-as-int n := k, from 4
  have s5 : 0 ≤ k := by
    have hI : 0 ≤ k := by parley_instance (((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := k))).mpr (by parley_side))
    exact hI
  -- 6. thm:odd-power-of-minus-one, from 5
  have s6 : ((-1) ^ (2 * k + 1) : ℚ) = -1 := by (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k) (by parley_side)); simp only [parley_zpow_toNat (n := 2 * k + 1) (h := le_trans (by norm_num) s3)] at h ⊢; exact_mod_cast h)
  -- 7. substitute 2·k + 1 = n (line 1) into line 6
  parley_subst_at s1 s6

end Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd
