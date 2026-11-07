module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
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
  have s1a : 0 < (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
  have s1b : (Int.gcd a b : ℤ) ∣ a := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
  have s1c : (Int.gcd a b : ℤ) ∣ b := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
  have s1d : ∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
  -- 2. both directions
  have s2 : a = (Int.gcd a b : ℤ) ↔ a ∣ b := by
    constructor
    · skip
      intro hD1
      -- 2.1. substitute a = gcd(a, b) (D1) into line 1
      have s2_1 : a ∣ b := by parley_subst_at hD1 s1c
      all_goals parley_side
    · skip
      intro hD2
      -- 2.2. mun:divides-self n := a
      have s2_2 : a ∣ a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := a)); parley_side)
      -- 2.3. join 2.2, D2
      have s2_3 : a ∣ a ∧ a ∣ b := by parley_side
      -- 2.4. instantiate e := a in line 1
      have s2_4 : a ∣ a ∧ a ∣ b → a ≤ (Int.gcd a b : ℤ) := by first | exact (s1d a (by parley_side)) | exact ((s1d a (by parley_side))).symm | simpa using (s1d a (by parley_side)) | exact_mod_cast (s1d a (by parley_side)) | (have h := (s1d a (by parley_side)); parley_side)
      -- 2.5. mun:modus-ponens P := a divides a and a divides b, Q := a ≤ gcd(a, b), from 2.3, 2.4
      have s2_5 : a ≤ (Int.gcd a b : ℤ) := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a ∣ a ∧ a ∣ b) (Q := a ≤ (Int.gcd a b : ℤ)) s2_4 (by parley_side))] | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a ∣ a ∧ a ∣ b) (Q := a ≤ (Int.gcd a b : ℤ)) s2_4 (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a ∣ a ∧ a ∣ b) (Q := a ≤ (Int.gcd a b : ℤ)) s2_4 (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a ∣ a ∧ a ∣ b) (Q := a ≤ (Int.gcd a b : ℤ)) s2_4 (by parley_side)); parley_side)
      -- 2.6. mun:divides-le e := gcd(a, b), m := a, from 1
      have s2_6 : (Int.gcd a b : ℤ) ≤ a := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_side) (m := a) (by parley_side) s1b)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_side) (m := a) (by parley_side) s1b); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_side) (m := a) (by parley_side) s1b) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_side) (m := a) (by parley_side) s1b); parley_side)
      -- 2.7. antisymmetry, from 2.5, 2.6
      have s2_7 : a = (Int.gcd a b : ℤ) := by parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.GcdEqualsFirst.GcdEqualsFirst
