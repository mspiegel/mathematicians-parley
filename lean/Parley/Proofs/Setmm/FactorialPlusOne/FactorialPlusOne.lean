module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/factorial-plus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FactorialPlusOne.FactorialPlusOne

set_option maxHeartbeats 400000 in
theorem factorial_plus_one (M : ℤ) (hH1 : 0 ≤ M) (N : ℤ) (hH2 : 0 < N) (hH3 : 1 < N) (hH4 : N ≤ M) :
    ¬ (∃ m : ℤ, (m : ℚ) = ((LeanBridges.Counting.factorial M : ℚ) + 1) / (N : ℚ)) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ m : ℤ, (m : ℚ) = ((LeanBridges.Counting.factorial M : ℚ) + 1) / (N : ℚ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℤ, (m : ℚ) = ((LeanBridges.Counting.factorial M : ℚ) + 1) / (N : ℚ) := by parley_suppose hc_hS
    -- 1. inequalities, from H2
    have s1 : 0 < N := by parley_order
    -- 2. transitivity, from 1, H4
    have s2 : 0 < M := by parley_order
    -- 3. mun:pos-int-nat m := M, from 2
    have s3 : 0 < M := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := M) s2) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := M) s2)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := M) s2) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := M) s2) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := M) s2); parley_side)
    -- 4. mun:factorial-divisible n := M, m := N, from H4, 3
    have s4 : N ∣ (LeanBridges.Counting.factorial M : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) hH4) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) hH4)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) hH4) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) hH4) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) hH4); parley_side)
    -- 5. algebra
    have s5 : (LeanBridges.Counting.factorial M : ℚ) + 1 = (N : ℚ) * (((LeanBridges.Counting.factorial M : ℚ) + 1) / (N : ℚ)) := by parley_ring
    -- 6. exhibit, from S, 5
    have s6 : ∃ k : ℤ, (LeanBridges.Counting.factorial M : ℤ) + 1 = N * k := ⟨Classical.choose hS, by have := Classical.choose_spec hS; parley_side⟩
    -- 7. def:divides d := N, n := M! + 1, from 6
    have s7 : N ∣ (LeanBridges.Counting.factorial M : ℤ) + 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := N) (n := (LeanBridges.Counting.factorial M : ℤ) + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := N) (n := (LeanBridges.Counting.factorial M : ℤ) + 1))).mpr (by parley_side); parley_side)
    -- 8. mun:divides-difference d := N, a := M! + 1, b := M!, from 4, 7
    have s8 : N ∣ (LeanBridges.Counting.factorial M : ℤ) + 1 - (LeanBridges.Counting.factorial M : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := N) (a := (LeanBridges.Counting.factorial M : ℤ) + 1) (b := (LeanBridges.Counting.factorial M : ℤ)) s7 s4) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := N) (a := (LeanBridges.Counting.factorial M : ℤ) + 1) (b := (LeanBridges.Counting.factorial M : ℤ)) s7 s4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := N) (a := (LeanBridges.Counting.factorial M : ℤ) + 1) (b := (LeanBridges.Counting.factorial M : ℤ)) s7 s4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := N) (a := (LeanBridges.Counting.factorial M : ℤ) + 1) (b := (LeanBridges.Counting.factorial M : ℤ)) s7 s4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := N) (a := (LeanBridges.Counting.factorial M : ℤ) + 1) (b := (LeanBridges.Counting.factorial M : ℤ)) s7 s4); parley_side)
    -- 9. substitute
    have s9 : N ∣ (1 : ℤ) := by
      have c1 : (LeanBridges.Counting.factorial M : ℤ) + 1 - (LeanBridges.Counting.factorial M : ℤ) = 1 := by parley_ring
      have row1 : N ∣ (1 : ℤ) := by parley_subst_at c1 s8
      exact row1
    -- 10. mun:divides-one d := N, from 9
    have s10 : N = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9); parley_side)
    -- 11. inequalities
    have s11 : N ≠ 1 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.FactorialPlusOne.FactorialPlusOne
