module

public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/square-not-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareNotPrime.SquareNotPrime

set_option maxHeartbeats 400000 in
theorem square_not_prime (A : ℤ) :
    ¬ Nat.Prime (A ^ 2).toNat := by
  -- the theorem. contradiction
  have sThm : ¬ Nat.Prime (A ^ 2).toNat := by
    by_contra hc_hS
    have hS : Nat.Prime (A ^ 2).toNat := by parley_suppose hc_hS
    -- 1. mun:prime-nat p := A², from S
    have s1 : 0 < A ^ 2 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := A ^ 2) hS) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := A ^ 2) hS)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := A ^ 2) hS) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := A ^ 2) hS) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := A ^ 2) hS); parley_side)
    -- 2. def:prime p := A², from S, 1
    have s2 : A ^ 2 > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side); parley_side)
    -- 3. mun:abs-square x := A
    have s3 : abs A ^ 2 = A ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_square (x := A))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); parley_side)
    -- 4. contradiction
    have s4 : abs A ≠ 0 := by
      by_contra hc_hS2
      have hS2 : abs A = 0 := by parley_suppose hc_hS2
      -- 4.1. substitute |A| = 0 (S2) into line 3
      have s4_1 : 0 ^ 2 = A ^ 2 := by parley_subst_at hS2 s3
      -- 4.2. inequalities
      have s4_2 : 0 ^ 2 ≥ A ^ 2 := by parley_order
      -- 4.3. inequalities, from 4.2
      have s4_3 : ¬ A ^ 2 > 1 := by parley_side
      all_goals parley_side
    -- 5. mun:nat0-nonzero m := |A|, from 4
    have s5 : 0 < abs A := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := abs A) (by parley_side) s4) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := abs A) (by parley_side) s4)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := abs A) (by parley_side) s4) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := abs A) (by parley_side) s4) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := abs A) (by parley_side) s4); parley_side)
    -- 6. algebra, from 3
    have s6 : A ^ 2 = abs A * abs A := by linear_combination (norm := parley_norm) (-1) * s3
    -- 7. def:divides d := |A|, n := A², from 6
    have s7 : abs A ∣ A ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := abs A) (n := A ^ 2))).mpr ⟨abs A, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := abs A) (n := A ^ 2))).mpr ⟨abs A, by parley_side⟩; parley_side)
    -- 8. def:prime p := A², from S, 1
    have s8 : ∀ d : ℤ, 0 < d → d ∣ A ^ 2 → d = 1 ∨ d = A ^ 2 := by first | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) (by parley_side))).mp (by parley_side)).2; parley_side)
    -- 9. instantiate d := |A| in line 8, from 5
    have s9 : abs A ∣ A ^ 2 → abs A = 1 ∨ abs A = A ^ 2 := by first | exact (s8 (abs A) (by parley_side)) | exact ((s8 (abs A) (by parley_side))).symm | simpa using (s8 (abs A) (by parley_side)) | exact_mod_cast (s8 (abs A) (by parley_side)) | (have h := (s8 (abs A) (by parley_side)); parley_side)
    -- 10. mun:modus-ponens, from 7, 9
    have s10 : abs A = 1 ∨ abs A = A ^ 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := abs A ∣ A ^ 2) (Q := abs A = 1 ∨ abs A = A ^ 2) s9 s7) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := abs A ∣ A ^ 2) (Q := abs A = 1 ∨ abs A = A ^ 2) s9 s7)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := abs A ∣ A ^ 2) (Q := abs A = 1 ∨ abs A = A ^ 2) s9 s7) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := abs A ∣ A ^ 2) (Q := abs A = 1 ∨ abs A = A ^ 2) s9 s7) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := abs A ∣ A ^ 2) (Q := abs A = 1 ∨ abs A = A ^ 2) s9 s7); parley_side)
    -- 11. cases, from 10
    have s11 : abs A = 1 := by
      rcases s10 with hC1 | hC2
      · skip
        all_goals parley_side
      · skip
        -- 11.1. transitivity, from 6, C2
        have s11_1 : abs A * abs A = 1 * abs A := by parley_side
        -- 11.2. mun:multiply-cancel a := |A|, b := 1, c := |A|, from 4, 11.1
        have s11_2 : abs A = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) (by parley_side)); parley_side)
        all_goals parley_side
    -- 12. substitute |A| = 1 (line 11) into line 3
    have s12 : 1 ^ 2 = A ^ 2 := by parley_subst_at s11 s3
    -- 13. inequalities
    have s13 : 1 ^ 2 ≥ A ^ 2 := by parley_order
    -- 14. inequalities, from 13
    have s14 : ¬ A ^ 2 > 1 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.SquareNotPrime.SquareNotPrime
