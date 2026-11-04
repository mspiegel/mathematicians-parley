module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/prime-divides-predecessor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDividesPredecessor.PrimeDividesPredecessor

theorem prime_divides_predecessor (P : ℕ) (hH1 : 0 < P) (hH2 : Nat.Prime P) (A : ℤ) (hH4 : (P : ℤ) ∣ A - 1) :
    ¬ (P : ℤ) ∣ A := by
  -- 1. def:prime p := P, from H2
  have s1 : (P : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. contradiction
  have s2 : ¬ (P : ℤ) ∣ A := by
    by_contra hc_hS
    have hS : (P : ℤ) ∣ A := by parley_suppose hc_hS
    -- 2.1. mun:divides-difference d := P, a := A, b := A − 1, from H4, S
    have s2_1 : (P : ℤ) ∣ A - (A - 1) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (P : ℤ)) (a := A) (b := A - 1) hS hH4) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (P : ℤ)) (a := A) (b := A - 1) hS hH4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (P : ℤ)) (a := A) (b := A - 1) hS hH4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (P : ℤ)) (a := A) (b := A - 1) hS hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (P : ℤ)) (a := A) (b := A - 1) hS hH4); parley_side)
    -- 2.2. substitute
    have s2_2 : (P : ℤ) ∣ (1 : ℤ) := by
      have c1 : A - (A - 1) = 1 := by parley_ring
      have row1 : (P : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s2_1
      exact row1
    -- 2.3. mun:divides-one d := P, from 2.2
    have s2_3 : (P : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) (by parley_side)); parley_side)
    -- 2.4. inequalities
    have s2_4 : (P : ℤ) ≠ 1 := by parley_side
    all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.PrimeDividesPredecessor.PrimeDividesPredecessor
