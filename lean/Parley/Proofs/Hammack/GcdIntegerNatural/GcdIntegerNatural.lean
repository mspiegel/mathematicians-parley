module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
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

set_option maxHeartbeats 400000 in
theorem gcd_integer_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    0 < (Int.gcd a b : ℤ) ∧ (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b := by
  -- 1. thm:gcd-mod
  have s1 : (Int.gcd (a % b) b : ℤ) = (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side))
  -- 2. mun:mod-natural
  have s2 : 0 ≤ a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side))
  -- 3. mun:mod-less
  have s3 : a % b < b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) (by parley_side))
  -- 4. obtain q: mun:mod-remainder m := b, r := a mod b, from 2, 3
  obtain ⟨q, s4⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := b) (by parley_side) (r := a % b) (by parley_side) s3)).mp (by parley_side)
  -- 5. axi:excluded-middle P := a mod b = 0
  have s5 : a % b = 0 ∨ a % b ≠ 0 := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a % b = 0))
  -- 6. cases, from 5
  have s6a_all : 0 < (Int.gcd a b : ℤ) ∧ (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b := by
    rcases s5 with hC1 | hC2
    · skip
      -- 6.1. calculation
      have s6_1 : (Int.gcd a b : ℤ) = b := by
        calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := by parley_side
          _ = (Int.gcd (0 : ℤ) b : ℤ) := by parley_subst hC1
          _ = (Int.gcd b (0 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (0 : ℤ)) (b := b))
          _ = b := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := b) (by parley_side))
      -- 6.2. mun:divides-self n := b
      have s6_2 : b ∣ b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := b))
      -- 6.3. algebra, from C1, 4
      have s6_3 : a = b * q := by linear_combination (norm := parley_norm) hC1 + (-1) * s4
      -- 6.4. def:divides d := b, n := a, from 6.3
      have s6_4 : b ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := b) (n := a))).mpr ⟨q, s6_3⟩
      -- 6.5. join H2, 6.2, 6.4
      have s6_5a : 0 < b := by parley_side
      have s6_5b : b ∣ a := by parley_side
      have s6_5c : b ∣ b := by parley_side
      -- 6.6. substitute gcd(a, b) = b (line 6.1) into line 6.5
      have s6_6a : 0 < (Int.gcd a b : ℤ) := by parley_subst_at s6_1 s6_5a
      have s6_6b : (Int.gcd a b : ℤ) ∣ a := by parley_subst_at s6_1 s6_5b
      have s6_6c : (Int.gcd a b : ℤ) ∣ b := by first | parley_put_at s6_1 s6_5b | parley_put_at s6_1 s6_5c | parley_subst_at s6_1 s6_5b | parley_subst_at s6_1 s6_5c
      exact ⟨s6_6a, s6_6b, s6_6c⟩
    · skip
      -- 6.7. mun:nat0-nonzero m := a mod b, from C2, 2
      have s6_7 : 0 < a % b := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := a % b) (by parley_side) hC2)
      -- 6.8. def:gcd a := a mod b, from 6.7
      have s6_8a : 0 < (Int.gcd (a % b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a % b) (by parley_side) (b := b) (by parley_side))
      have s6_8b : (Int.gcd (a % b) b : ℤ) ∣ a % b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a % b) (by parley_side) (b := b) (by parley_side))
      have s6_8c : (Int.gcd (a % b) b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a % b) (by parley_side) (b := b) (by parley_side))
      -- 6.9. substitute gcd(a mod b, b) = gcd(a, b) (line 1) into line 6.8
      have r80_1 : 0 < a % b := by parley_side
      have s6_9a : 0 < (Int.gcd a b : ℤ) := by first | parley_subst_at s1 s6_8a | (have e_nat : Int.gcd (a % b) b = Int.gcd a b := by exact_mod_cast s1; parley_subst_at e_nat s6_8a)
      have s6_9b : (Int.gcd a b : ℤ) ∣ a % b := by first | parley_subst_at s1 s6_8b | (have e_nat : Int.gcd (a % b) b = Int.gcd a b := by exact_mod_cast s1; parley_subst_at e_nat s6_8b)
      have s6_9c : (Int.gcd a b : ℤ) ∣ b := by first | parley_subst_at s1 s6_8c | (have e_nat : Int.gcd (a % b) b = Int.gcd a b := by exact_mod_cast s1; parley_subst_at e_nat s6_8c)
      -- 6.10. mun:divides-multiple e := gcd(a, b), a := b, x := q, from 6.9
      have s6_10 : (Int.gcd a b : ℤ) ∣ b * q := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd a b : ℤ)) (a := b) (x := q) s6_9c)
      -- 6.11. mun:divides-sum d := gcd(a, b), a := b·q, b := a mod b, from 6.9, 6.10
      have s6_11 : (Int.gcd a b : ℤ) ∣ b * q + a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd a b : ℤ)) (a := b * q) (b := a % b) s6_10 s6_9b)
      -- 6.12. substitute
      have s6_12 : (Int.gcd a b : ℤ) ∣ a := by
        have c1 : b * q + a % b = a := by linear_combination (norm := parley_norm) s4
        have row1 : (Int.gcd a b : ℤ) ∣ a := by parley_subst_at c1 s6_11
        exact row1
      -- 6.13. join 6.9, 6.12
      have s6_13a : 0 < (Int.gcd a b : ℤ) := by parley_side
      have s6_13b : (Int.gcd a b : ℤ) ∣ a := by parley_side
      have s6_13c : (Int.gcd a b : ℤ) ∣ b := by parley_side
      exact ⟨s6_13a, s6_13b, s6_13c⟩
  obtain ⟨s6a, s6b, s6c⟩ := s6a_all
  exact ⟨s6a, s6b, s6c⟩

end Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural
