module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/gcd-integer-natural.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural

theorem gcd_integer_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    0 < (Int.gcd a b : ℤ) ∧ (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b := by
  -- 1. thm:gcd-mod
  have s1 : (Int.gcd (a % b) b : ℤ) = (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) hH2)
  -- 2. mun:mod-natural
  have s2 : 0 ≤ a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) hH2)
  -- 3. mun:mod-less
  have s3 : a % b < b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) hH2)
  -- 4. obtain q: mun:mod-remainder m := b, r := a mod b, from 2, 3
  obtain ⟨q, s4⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := b) hH2 (r := a % b) s2 s3)).mp rfl
  -- 5. axi:excluded-middle P := a mod b = 0
  have s5 : a % b = 0 ∨ a % b ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a % b = 0))
  -- 6. cases, from 5
  have s6a_all : 0 < (Int.gcd a b : ℤ) ∧ (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b := by
    rcases s5 with hC1 | hC2
    · skip
      -- 6.1. calculation
      have s6_1 : (Int.gcd a b : ℤ) = b := by
        calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := by exact s1.symm
          _ = (Int.gcd (0 : ℤ) b : ℤ) := by (have h := congrArg (fun t : ℤ => (Int.gcd t b : ℤ)) hC1; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (Int.gcd b (0 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (0 : ℤ)) (b := b))
          _ = b := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := b) (le_of_lt hH2))
      -- 6.2. mun:divides-self n := b
      have s6_2 : b ∣ b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := b))
      -- 6.3. algebra, from C1, 4
      have s6_3 : a = b * q := by linear_combination (norm := parley_norm) hC1 + (-1) * s4
      -- 6.4. def:divides d := b, n := a, from 6.3
      have s6_4 : b ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := b) (n := a))).mpr ⟨q, s6_3⟩
      -- 6.5. join H2, 6.2, 6.4
      have s6_5a : 0 < b := hH2
      have s6_5b : b ∣ a := s6_4
      have s6_5c : b ∣ b := s6_2
      -- 6.6. substitute gcd(a, b) = b (line 6.1) into line 6.5
      have s6_6a : 0 < (Int.gcd a b : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) s6_1.symm s6_5a; push_cast at h ⊢; all_goals exact_mod_cast h)
      have s6_6b : (Int.gcd a b : ℤ) ∣ a := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ a)) s6_1.symm s6_5b; push_cast at h ⊢; all_goals exact_mod_cast h)
      have s6_6c : (Int.gcd a b : ℤ) ∣ b := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ b)) s6_1.symm s6_5c; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact ⟨s6_6a, s6_6b, s6_6c⟩
    · skip
      -- 6.7. mun:nat0-nonzero m := a mod b, from C2, 2
      have s6_7 : 0 < a % b := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := a % b) s2 hC2)
      -- 6.8. def:gcd a := a mod b, from 6.7
      have s6_8a : 0 < (Int.gcd (a % b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a % b) s6_7 (b := b) hH2)
      have s6_8b : (Int.gcd (a % b) b : ℤ) ∣ a % b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a % b) s6_7 (b := b) hH2)
      have s6_8c : (Int.gcd (a % b) b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a % b) s6_7 (b := b) hH2)
      -- 6.9. substitute gcd(a mod b, b) = gcd(a, b) (line 1) into line 6.8
      have r80_1 : 0 < a % b := by exact s6_7
      have s6_9a : 0 < (Int.gcd a b : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) s1 s6_8a; push_cast at h ⊢; all_goals exact_mod_cast h)
      have s6_9b : (Int.gcd a b : ℤ) ∣ a % b := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ a % b)) s1 s6_8b; push_cast at h ⊢; all_goals exact_mod_cast h)
      have s6_9c : (Int.gcd a b : ℤ) ∣ b := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ b)) s1 s6_8c; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 6.10. mun:divides-multiple e := gcd(a, b), a := b, x := q, from 6.9
      have s6_10 : (Int.gcd a b : ℤ) ∣ b * q := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd a b : ℤ)) (a := b) (x := q) s6_9c)
      -- 6.11. mun:divides-sum d := gcd(a, b), a := b·q, b := a mod b, from 6.9, 6.10
      have s6_11 : (Int.gcd a b : ℤ) ∣ b * q + a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd a b : ℤ)) (a := b * q) (b := a % b) s6_10 s6_9b)
      -- 6.12. substitute
      have s6_12 : (Int.gcd a b : ℤ) ∣ a := by
        have c1 : b * q + a % b = a := by linear_combination (norm := parley_norm) s4
        have row1 : (Int.gcd a b : ℤ) ∣ a := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd a b : ℤ) ∣ t)) c1 s6_11; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 6.13. join 6.9, 6.12
      have s6_13a : 0 < (Int.gcd a b : ℤ) := s6_9a
      have s6_13b : (Int.gcd a b : ℤ) ∣ a := s6_12
      have s6_13c : (Int.gcd a b : ℤ) ∣ b := s6_9c
      exact ⟨s6_13a, s6_13b, s6_13c⟩
  obtain ⟨s6a, s6b, s6c⟩ := s6a_all
  exact ⟨s6a, s6b, s6c⟩

end Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural
