module

public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/lcm-equals-first.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LcmEqualsFirst.LcmEqualsFirst

set_option maxHeartbeats 400000 in
theorem lcm_equals_first (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) :
    (a = (Int.lcm a b : ℤ) ↔ b ∣ a) := by
  -- 1. def:lcm
  have s1 : b ∣ (Int.lcm a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_lcm_3 (a := a) (b := b))
  -- 2. def:lcm
  have s2 : a ∣ (Int.lcm a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b))
  -- 3. def:lcm
  have s3 : 0 ≤ (Int.lcm a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_lcm_1 (a := a) (b := b))
  -- 4. def:lcm
  have s4 : ∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k := by exact (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b))
  -- 5. both directions
  constructor
  · skip
    intro hD1
    -- 5.1. substitute a = lcm(a, b) (D1) into line 1
    parley_subst_at hD1 s1
  · skip
    intro hD2
    -- 5.2. mun:divides-self n := a
    have s5_2 : a ∣ a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a))
    -- 5.3. join 5.2, D2
    have s5_3a : a ∣ a := by parley_side
    have s5_3b : b ∣ a := by parley_side
    -- 5.4. instantiate k := a in line 4
    have s5_4 : a ∣ a ∧ b ∣ a → (Int.lcm a b : ℤ) ∣ a := by exact (s4 a)
    -- 5.5. mun:modus-ponens P := a divides a and b divides a, from 5.3, 5.4
    have s5_5 : (Int.lcm a b : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a ∣ a ∧ b ∣ a) (Q := (Int.lcm a b : ℤ) ∣ a) s5_4 (by parley_side))
    -- 5.6. contradiction
    have s5_6 : (Int.lcm a b : ℤ) ≠ 0 := by
      intro hS
      -- 5.6.1. substitute lcm(a, b) = 0 (S) into line 5.5
      have s5_6_1 : (0 : ℤ) ∣ a := by first | parley_subst_at hS s5_5 | (have e_nat : Int.lcm a b = 0 := by exact_mod_cast hS; parley_subst_at e_nat s5_5)
      -- 5.6.2. mun:zero-divides n := a, from 5.6.1
      have s5_6_2 : a = 0 := ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := a))).mp s5_6_1
      -- 5.6.3. inequalities, from H1
      have s5_6_3 : a ≠ 0 := by parley_side
      exact s5_6_3 s5_6_2
    -- 5.7. inequalities, from 3, 5.6
    have s5_7 : 0 < (Int.lcm a b : ℤ) := by parley_order
    -- 5.8. mun:pos-int-nat m := lcm(a, b), from 5.7
    have s5_8 : 0 < (Int.lcm a b : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (Int.lcm a b : ℤ)) s5_7)
    -- 5.9. mun:divides-le e := lcm(a, b), m := a, from 5.5, 5.8
    have s5_9 : (Int.lcm a b : ℤ) ≤ a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.lcm a b : ℤ)) (by parley_side) (m := a) (by parley_side) s5_5)
    -- 5.10. mun:divides-le e := a, m := lcm(a, b), from 2, 5.8
    have s5_10 : a ≤ (Int.lcm a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := a) (by parley_side) (m := (Int.lcm a b : ℤ)) (by parley_side) s2)
    -- 5.11. antisymmetry, from 5.9, 5.10
    parley_side

end Parley.Proofs.Hammack.LcmEqualsFirst.LcmEqualsFirst
