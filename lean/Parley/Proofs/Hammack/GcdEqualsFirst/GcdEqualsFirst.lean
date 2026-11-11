module

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
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/gcd-equals-first.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdEqualsFirst.GcdEqualsFirst

theorem gcd_equals_first (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) :
    (a = (Int.gcd a b : ℤ) ↔ a ∣ b) := by
  -- 1. def:gcd
  have s1a : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) hH1 (b := b) hH2)
  have s1b : (Int.gcd a b : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) hH1 (b := b) hH2)
  have s1c : (Int.gcd a b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) hH1 (b := b) hH2)
  have s1d : ∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) hH1 (b := b) hH2)
  -- 2. both directions
  constructor
  · skip
    intro hD1
    -- 2.1. substitute a = gcd(a, b) (D1) into line 1
    (have h := Eq.subst (motive := (fun t : ℤ => t ∣ b)) hD1.symm s1c; push_cast at h ⊢; all_goals exact_mod_cast h)
  · skip
    intro hD2
    -- 2.2. mun:divides-self n := a
    have s2_2 : a ∣ a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a))
    -- 2.3. join 2.2, D2
    have s2_3 : a ∣ a ∧ a ∣ b := by parley_side
    -- 2.4. instantiate e := a in line 1
    have s2_4 : a ∣ a ∧ a ∣ b → a ≤ (Int.gcd a b : ℤ) := by exact (s1d a hH1)
    -- 2.5. mun:modus-ponens P := a divides a and a divides b, Q := a ≤ gcd(a, b), from 2.3, 2.4
    have s2_5 : a ≤ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a ∣ a ∧ a ∣ b) (Q := a ≤ (Int.gcd a b : ℤ)) s2_4 s2_3)
    -- 2.6. mun:divides-le e := gcd(a, b), m := a, from 1
    have s2_6 : (Int.gcd a b : ℤ) ≤ a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) s1a (m := a) hH1 s1b)
    -- 2.7. antisymmetry, from 2.5, 2.6
    parley_side

end Parley.Proofs.Hammack.GcdEqualsFirst.GcdEqualsFirst
