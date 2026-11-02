module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/harmonic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Harmonic.HarmonicBlock

theorem harmonic_block (j : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) ≥ (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 := by
  -- 1. mun:exponent-step a := 2, m := j
  have s1 : (2 ^ (j + 1) : ℤ) = 2 ^ j * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j)); parley_side)
  -- 2. mun:power-nat a := 2, m := j
  have s2 : 0 < 2 ^ j := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j)); parley_side)
  -- 3. mun:power-nat a := 2, m := j + 1
  have s3 : 0 < 2 ^ (j + 1) := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j + 1)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j + 1))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j + 1)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j + 1)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := j + 1)); parley_side)
  -- 4. inequalities, from 2
  have s4 : (2 ^ j : ℤ) ≤ 2 ^ j * 2 := by parley_side
  -- 5. transitivity, from 4, 1
  have s5 : (2 ^ j : ℤ) ≤ 2 ^ (j + 1) := by parley_side
  -- 6. proof
  -- what this block shows, Lean's types give
  -- 7. mun:sum-split a := 1, b := 2^j, c := 2^(j + 1), from 5, 6
  have r42_1 : (1 : ℤ) ≤ 2 ^ j + 1 := by parley_side
  have s7 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j : ℤ), (1 / (k : ℚ) : ℚ)) + (∑ k ∈ Finset.Icc (2 ^ j + 1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j : ℤ)) (c := (2 ^ (j + 1) : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 8. inequalities, from 2
  have s8 : (0 : ℤ) < 2 ^ j + 1 := by parley_side
  -- 9. proof
  have s9 : ∀ k : ℤ, k ∈ Finset.Icc (2 ^ j + 1) (2 ^ (j + 1)) → 1 / 2 ^ (j + 1) ≤ 1 / (k : ℚ) := by
    intro k hK2
    -- 9.1. mun:range-bounds a := 2^j + 1, b := 2^(j + 1), from K2
    have s9_1a : 2 ^ j + 1 ≤ k := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side)); parley_side)
    have s9_1b : k ≤ 2 ^ (j + 1) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (k := k) (by parley_side)); parley_side)
    -- 9.2. transitivity, from 8, 9.1
    have s9_2 : k > 0 := by parley_side
    -- 9.3. mun:reciprocal-order x := k, y := 2^(j + 1), from 9.1
    have r59_1 : k > 0 := by parley_side
    have r59_2 : (2 ^ (j + 1) : ℤ) > 0 := by parley_side
    have s9_3 : 1 / 2 ^ (j + 1) ≤ 1 / (k : ℚ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (k : ℚ)) (by parley_side) (y := (2 ^ (j + 1) : ℚ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (k : ℚ)) (by parley_side) (y := (2 ^ (j + 1) : ℚ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (k : ℚ)) (by parley_side) (y := (2 ^ (j + 1) : ℚ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (k : ℚ)) (by parley_side) (y := (2 ^ (j + 1) : ℚ)) (by parley_side))).mp (by parley_side); parley_side)
    all_goals parley_side
  -- 10. proof
  -- what this block shows, Lean's types give
  -- 11. mun:sum-le a := 2^j + 1, b := 2^(j + 1), from 9
  have s11 : (∑ k ∈ Finset.Icc (2 ^ j + 1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / 2 ^ (j + 1) : ℚ)) ≤ (∑ k ∈ Finset.Icc (2 ^ j + 1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (1 / 2 ^ (j + 1) : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (1 / 2 ^ (j + 1) : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (1 / 2 ^ (j + 1) : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (1 / 2 ^ (j + 1) : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side)); parley_side)
  -- 12. inequalities, from 2
  have s12 : (2 ^ j + 1 : ℤ) ≤ 2 ^ j * 2 := by parley_side
  -- 13. transitivity, from 12, 1
  have s13 : (2 ^ j + 1 : ℤ) ≤ 2 ^ (j + 1) := by parley_side
  -- 14. mun:sum-constant a := 2^j + 1, b := 2^(j + 1), c := 1/2^(j + 1)
  have r88_1 : (2 ^ j + 1 : ℤ) ≤ 2 ^ (j + 1) := by parley_side
  have s14 : (∑ k ∈ Finset.Icc (2 ^ j + 1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / 2 ^ (j + 1) : ℚ)) = (2 ^ (j + 1) - (2 ^ j + 1) + 1) * (1 / 2 ^ (j + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j + 1 : ℤ)) (b := (2 ^ (j + 1) : ℤ)) (by parley_side) (c := (1 / 2 ^ (j + 1) : ℚ))); parley_side)
  -- 15. calculation
  have s15 : ((2 ^ (j + 1) - (2 ^ j + 1) + 1) * (1 / 2 ^ (j + 1)) : ℚ) = 1 / 2 := by
    calc ((2 ^ (j + 1) - (2 ^ j + 1) + 1) * (1 / 2 ^ (j + 1)) : ℚ) = (2 ^ j * 2 - (2 ^ j + 1) + 1) * (1 / (2 ^ j * 2)) := by
          have s1_w : (2 ^ (j + 1) : ℚ) = 2 ^ j * 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s1_w | parley_subst s1
      _ = 1 / 2 := by parley_ring
  -- 16. transitivity, from 15, 14, 11
  have s16 : 1 / 2 ≤ (∑ k ∈ Finset.Icc (2 ^ j + 1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) := by parley_side
  -- 17. inequalities
  have s17 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j : ℤ), (1 / (k : ℚ) : ℚ)) + (∑ k ∈ Finset.Icc (2 ^ j + 1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) := by parley_side
  -- 18. transitivity, from 17, 7
  have s18 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (j + 1) : ℤ), (1 / (k : ℚ) : ℚ)) ≥ (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 := by parley_side
  all_goals parley_side

end Parley.Proofs.Wiedijk.Harmonic.HarmonicBlock
