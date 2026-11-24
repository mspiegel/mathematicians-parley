module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
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
  -- 2. mun:mod-less
  have s2 : a % b < b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) hH2)
  -- 3. obtain q: mun:mod-remainder m := b, r := a mod b, from 2
  obtain ⟨q, s3⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := b) hH2 (r := a % b) (Int.emod_nonneg _ (ne_of_gt (hH2))) s2)).mp rfl
  -- 4. axi:excluded-middle P := a mod b = 0
  have s4 : a % b = 0 ∨ a % b ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a % b = 0))
  -- 5. cases, from 4
  have s5a_all : 0 < (Int.gcd a b : ℤ) ∧ (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b := by
    rcases s4 with hC1 | hC2
    · skip
      -- 5.1. calculation
      have s5_1 : (Int.gcd a b : ℤ) = b := by
        calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := s1.symm
          _ = (Int.gcd (0 : ℤ) b : ℤ) := by (have h := congrArg (fun t : ℤ => (Int.gcd t b : ℤ)) hC1; push_cast at h ⊢; exact_mod_cast h)
          _ = (Int.gcd b (0 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (0 : ℤ)) (b := b))
          _ = b := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := b) (le_of_lt hH2))
      -- 5.2. mun:divides-self n := b
      have s5_2 : b ∣ b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := b))
      -- 5.3. algebra, from C1, 3
      have s5_3 : a = b * q := by linear_combination hC1 + (-1) * s3
      -- 5.4. def:divides d := b, n := a, from 5.3
      have s5_4 : b ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := b) (n := a))).mpr ⟨q, s5_3⟩
      -- 5.5. join H2, 5.2, 5.4
      have s5_5a : 0 < b := hH2
      have s5_5b : b ∣ a := s5_4
      have s5_5c : b ∣ b := s5_2
      -- 5.6. substitute gcd(a, b) = b (line 5.1) into line 5.5
      have s5_6a : 0 < (Int.gcd a b : ℤ) := Eq.subst (motive := (fun t : ℤ => 0 < t)) s5_1.symm s5_5a
      have s5_6b : (Int.gcd a b : ℤ) ∣ a := Eq.subst (motive := (fun t : ℤ => t ∣ a)) s5_1.symm s5_5b
      have s5_6c : (Int.gcd a b : ℤ) ∣ b := Eq.subst (motive := (fun t : ℤ => t ∣ b)) s5_1.symm s5_5c
      exact ⟨s5_6a, s5_6b, s5_6c⟩
    · skip
      -- 5.7. mun:nat0-nonzero m := a mod b, from C2
      have s5_7 : 0 < a % b := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := a % b) (Int.emod_nonneg _ (ne_of_gt (hH2))) hC2)
      -- 5.8. def:gcd a := a mod b, from 5.7
      have s5_8a : 0 < (Int.gcd (a % b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a % b) s5_7 (b := b) hH2)
      have s5_8b : (Int.gcd (a % b) b : ℤ) ∣ a % b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a % b) s5_7 (b := b) hH2)
      have s5_8c : (Int.gcd (a % b) b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a % b) s5_7 (b := b) hH2)
      -- 5.9. substitute gcd(a mod b, b) = gcd(a, b) (line 1) into line 5.8
      have s5_9a : 0 < (Int.gcd a b : ℤ) := Eq.subst (motive := (fun t : ℤ => 0 < t)) s1 s5_8a
      have s5_9b : (Int.gcd a b : ℤ) ∣ a % b := Eq.subst (motive := (fun t : ℤ => t ∣ a % b)) s1 s5_8b
      have s5_9c : (Int.gcd a b : ℤ) ∣ b := Eq.subst (motive := (fun t : ℤ => t ∣ b)) s1 s5_8c
      -- 5.10. mun:divides-multiple e := gcd(a, b), a := b, x := q, from 5.9
      have s5_10 : (Int.gcd a b : ℤ) ∣ b * q := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd a b : ℤ)) (a := b) (x := q) s5_9c)
      -- 5.11. mun:divides-sum d := gcd(a, b), a := b·q, b := a mod b, from 5.9, 5.10
      have s5_11 : (Int.gcd a b : ℤ) ∣ b * q + a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd a b : ℤ)) (a := b * q) (b := a % b) s5_10 s5_9b)
      -- 5.12. substitute
      have s5_12 : (Int.gcd a b : ℤ) ∣ a := by
        have c1 : b * q + a % b = a := by linear_combination s3
        have row1 : (Int.gcd a b : ℤ) ∣ a := Eq.subst (motive := (fun t : ℤ => (Int.gcd a b : ℤ) ∣ t)) c1 s5_11
        exact row1
      -- 5.13. join 5.9, 5.12
      have s5_13a : 0 < (Int.gcd a b : ℤ) := s5_9a
      have s5_13b : (Int.gcd a b : ℤ) ∣ a := s5_12
      have s5_13c : (Int.gcd a b : ℤ) ∣ b := s5_9c
      exact ⟨s5_13a, s5_13b, s5_13c⟩
  obtain ⟨s5a, s5b, s5c⟩ := s5a_all
  exact ⟨s5a, s5b, s5c⟩

end Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural
