module

public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/factorial-plus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FactorialPlusOne.FactorialPlusOne

theorem factorial_plus_one (M : ℕ) (N : ℕ) (hH2 : 0 < N) (hH3 : 1 < (N : ℤ)) (hH4 : (N : ℤ) ≤ (M : ℤ)) :
    ¬ (∃ m : ℤ, (m : ℚ) = ((Parley.Library.factorial (M : ℤ) : ℚ) + 1) / (N : ℚ)) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ m : ℤ, (m : ℚ) = ((Parley.Library.factorial (M : ℤ) : ℚ) + 1) / (N : ℚ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℤ, (m : ℚ) = ((Parley.Library.factorial (M : ℤ) : ℚ) + 1) / (N : ℚ) := by parley_suppose hc_hS
    -- 1. inequalities, from H2
    have s1 : 0 < (N : ℤ) := by parley_side
    -- 2. transitivity, from 1, H4
    have s2 : 0 < (M : ℤ) := by parley_side
    -- 3. mun:pos-int-nat m := M, from 2
    have s3 : 0 < M := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (M : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (M : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (M : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := (M : ℤ)) (by parley_side))
    -- 4. mun:factorial-divisible n := M, m := N, from H4, 3
    have s4 : (N : ℤ) ∣ (Parley.Library.factorial (M : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) (by parley_side))
    -- 5. algebra
    have s5 : (Parley.Library.factorial (M : ℤ) : ℚ) + 1 = (N : ℚ) * (((Parley.Library.factorial (M : ℤ) : ℚ) + 1) / (N : ℚ)) := by parley_ring
    -- 6. exhibit, from S, 5
    have s6 : ∃ k : ℤ, (Parley.Library.factorial (M : ℤ) : ℤ) + 1 = (N : ℤ) * k := ⟨Classical.choose hS, by have := Classical.choose_spec hS; parley_side⟩
    -- 7. def:divides d := N, n := M! + 1, from 6
    have s7 : (N : ℤ) ∣ (Parley.Library.factorial (M : ℤ) : ℤ) + 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (N : ℤ)) (n := (Parley.Library.factorial (M : ℤ) : ℤ) + 1))).mpr (by parley_side)
    -- 8. mun:divides-difference d := N, a := M! + 1, b := M!, from 4, 7
    have s8 : (N : ℤ) ∣ (Parley.Library.factorial (M : ℤ) : ℤ) + 1 - (Parley.Library.factorial (M : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (N : ℤ)) (a := (Parley.Library.factorial (M : ℤ) : ℤ) + 1) (b := (Parley.Library.factorial (M : ℤ) : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (N : ℤ)) (a := (Parley.Library.factorial (M : ℤ) : ℤ) + 1) (b := (Parley.Library.factorial (M : ℤ) : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (N : ℤ)) (a := (Parley.Library.factorial (M : ℤ) : ℤ) + 1) (b := (Parley.Library.factorial (M : ℤ) : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (N : ℤ)) (a := (Parley.Library.factorial (M : ℤ) : ℤ) + 1) (b := (Parley.Library.factorial (M : ℤ) : ℤ)) (by parley_side) (by parley_side))
    -- 9. substitute
    have s9 : (N : ℤ) ∣ (1 : ℤ) := by
      have c1 : (Parley.Library.factorial (M : ℤ) : ℤ) + 1 - (Parley.Library.factorial (M : ℤ) : ℤ) = 1 := by parley_ring
      have row1 : (N : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s8
      exact row1
    -- 10. mun:divides-one d := N, from 9
    have s10 : (N : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
    -- 11. inequalities
    have s11 : (N : ℤ) ≠ 1 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.FactorialPlusOne.FactorialPlusOne
