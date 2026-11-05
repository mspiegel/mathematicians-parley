module

public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/prime-divisor-in-range.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDivisorInRange.PrimeDivisorInRange

theorem prime_divisor_in_range (N : ℕ) (hH1 : 0 < N) (I : ℤ) (hH2 : I ∈ Finset.Icc (2 : ℤ) (N : ℤ)) :
    (∃ p : ℕ, 0 < p ∧ ((Nat.Prime p ∧ (p : ℤ) ≤ (N : ℤ)) ∧ (p : ℤ) ∣ I)) := by
  -- 1. mun:range-bounds a := 2, b := N, k := I, from H2
  have s1 : 2 ≤ I := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2); parley_side)
  -- 2. mun:range-bounds a := 2, b := N, k := I, from H2
  have s2 : I ≤ (N : ℤ) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (N : ℤ)) (k := I) hH2); parley_side)
  -- 3. inequalities, from 1
  have s3 : 0 < I := by parley_order
  -- 4. mun:pos-int-nat m := I, from 3
  have s4 : 0 < I := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := I) s3) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := I) s3)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := I) s3) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := I) s3) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := I) s3); parley_side)
  lift I to ℕ using s4.le
  -- 5. inequalities, from 1
  have s5 : (I : ℤ) > 1 := by parley_order
  -- 6. obtain p: thm:prime-factor m := I, from 4, 5
  obtain ⟨p, s6a, ⟨s6b, s6c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := I) (by parley_side) (by parley_side))
  try lift p to ℕ using le_of_lt s6a
  -- 7. mun:divides-le e := p, m := I, from 4, 6
  have s7 : (p : ℤ) ≤ (I : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := p) (by parley_side) (m := I) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := p) (by parley_side) (m := I) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := p) (by parley_side) (m := I) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := p) (by parley_side) (m := I) (by parley_side) (by parley_side)); parley_side)
  -- 8. transitivity, from 7, 2
  have s8 : (p : ℤ) ≤ (N : ℤ) := by parley_order
  -- 9. exhibit, from 6, 8
  have s9 : ∃ p : ℕ, 0 < p ∧ ((Nat.Prime p ∧ (p : ℤ) ≤ (N : ℤ)) ∧ (p : ℤ) ∣ (I : ℤ)) := ⟨p, by parley_side, ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s9

end Parley.Proofs.Setmm.PrimeDivisorInRange.PrimeDivisorInRange
