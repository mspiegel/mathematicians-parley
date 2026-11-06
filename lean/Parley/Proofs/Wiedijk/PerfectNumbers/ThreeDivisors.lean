module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors

theorem three_divisors (m : ℤ) (hH1 : 0 < m) (e : ℤ) (hH2 : 0 < e) (hH3 : e ∣ m) (hH4 : 1 < e) (hH5 : e < m) :
    (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ 1 + e + m := by
  -- 1. mun:one-divides n := m
  have s1 : (1 : ℤ) ∣ m := by first | exact (Parley.Items.Stdlib.Divisibility.mun_one_divides (n := m)) | exact ((Parley.Items.Stdlib.Divisibility.mun_one_divides (n := m))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_one_divides (n := m)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_one_divides (n := m)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_one_divides (n := m)); parley_set_side)
  -- 2. mun:divides-self n := m
  have s2 : m ∣ m := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := m)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := m))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := m)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := m)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := m)); parley_set_side)
  -- 3. def:set-builder u := 1, from 1
  have s3 : (1 : ℤ) ∈ {d : ℤ | 0 < d ∧ d ∣ m} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := (1 : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := (1 : ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 4. def:set-builder u := e, from H3
  have s4 : e ∈ {d : ℤ | 0 < d ∧ d ∣ m} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := e))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := e))).mpr (by parley_set_side); parley_set_side)
  -- 5. def:set-builder u := m, from 2
  have s5 : m ∈ {d : ℤ | 0 < d ∧ d ∣ m} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := m))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := m))).mpr (by parley_set_side); parley_set_side)
  -- 6. mun:triple-subset, from 3, 4, 5
  have s6 : ({(1 : ℤ), e, m} : Set ℤ) ⊆ {d : ℤ | 0 < d ∧ d ∣ m} := by first | exact (Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5) | exact ((Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5); parley_set_side)
  -- 7. transitivity, from H4, H5
  have s7 : 1 < m := by parley_order
  -- 8. calculation
  have r302_1 : 1 ≠ e := by parley_set_side
  have r302_2 : 1 ≠ m := by parley_set_side
  have r302_3 : e ≠ m := by parley_set_side
  have s8 : (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ 1 + e + m := by
    calc (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ (∑ᶠ d ∈ ({(1 : ℤ), e, m} : Set ℤ), (d : ℤ)) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_sigma_part (Y := ({(1 : ℤ), e, m} : Set ℤ)) (n := m) (by parley_set_side) s6)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_sigma_part (Y := ({(1 : ℤ), e, m} : Set ℤ)) (n := m) (by parley_set_side) s6); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_sigma_part (Y := ({(1 : ℤ), e, m} : Set ℤ)) (n := m) (by parley_set_side) s6) | (have h := (Parley.Items.Stdlib.Divisibility.mun_sigma_part (Y := ({(1 : ℤ), e, m} : Set ℤ)) (n := m) (by parley_set_side) s6); parley_set_side)
      _ = 1 + e + m := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s8

end Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors
