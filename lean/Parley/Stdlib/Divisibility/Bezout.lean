module

public import AlgebraTactics
public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Stdlib.Divisibility.LeastCombinationDivides

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.Bezout

set_option maxHeartbeats 400000 in
theorem bezout (a : ℤ) (b : ℕ) (hH2 : 0 < b) :
    (∃ x : ℤ, ∃ y : ℤ, a * x + (b : ℤ) * y = (Int.gcd a (b : ℤ) : ℤ)) := by
  set S : Set ℤ := {t : ℤ | 0 < t ∧ (∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)} with hD1
  -- 1. algebra
  have s1 : (b : ℤ) = a * 0 + (b : ℤ) * 1 := by parley_ring
  -- 2. def:set-builder u := b, from D1, 1
  have s2 : (b : ℤ) ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n}) (u := (b : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n}) (u := (b : ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 3. mun:set-builder-subset, from D1
  have s3 : S ⊆ {n : ℤ | 0 < n} := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n})) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n})) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n})); parley_set_side)
  -- 4. obtain d: axi:well-ordering, from 2, 3
  obtain ⟨d, s4a, s4b⟩ := (Parley.Items.Stdlib.Numbers.axi_well_ordering (S := S) s3 (by parley_set_side))
  -- 5. def:subset, from 3
  have s5 : ∀ t ∈ S, 0 < t := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side); parley_set_side)
  -- 6. instantiate t := d in line 5, from 4
  have s6 : 0 < d := by first | exact (s5 d (by parley_set_side)) | exact ((s5 d (by parley_set_side))).symm | simpa using (s5 d (by parley_set_side)) | exact_mod_cast (s5 d (by parley_set_side)) | (have h := (s5 d (by parley_set_side)); parley_set_side)
  lift d to ℕ using s6.le
  -- 7. obtain x₀, y₀: def:set-builder u := d, from D1, 4
  obtain ⟨_, x₀, y₀, s7⟩ := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n}) (u := (d : ℤ)))).mp (by parley_set_side)
  -- 8. proof
  have s8 : ∀ x : ℤ, ∀ y : ℤ, 0 < a * x + (b : ℤ) * y → (d : ℤ) ≤ a * x + (b : ℤ) * y := by
    intro x
    intro y
    intro hK3
    -- 8.1. def:set-builder u := a·x + b·y, from D1, K3
    have s8_1 : a * x + (b : ℤ) * y ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n}) (u := a * x + (b : ℤ) * y))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + (b : ℤ) * n)) (X := {n : ℤ | 0 < n}) (u := a * x + (b : ℤ) * y))).mpr (by parley_set_side); parley_set_side)
    -- 8.2. instantiate s := a·x + b·y in line 4, from 8.1
    have s8_2 : (d : ℤ) ≤ a * x + (b : ℤ) * y := by first | linarith [(s4b (a * x + (b : ℤ) * y) (by parley_set_side))] | (have h := (s4b (a * x + (b : ℤ) * y) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4b (a * x + (b : ℤ) * y) (by parley_set_side)) | (have h := (s4b (a * x + (b : ℤ) * y) (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  -- 9. algebra
  have s9 : a = a * 1 + (b : ℤ) * 0 := by parley_ring
  -- 10. thm:least-combination-divides c := a, u := 1, v := 0, from 6, 7, 8, 9
  have s10 : (d : ℤ) ∣ a := by first | exact (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := a) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := a) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := a) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := a) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := a) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 11. thm:least-combination-divides c := b, u := 0, v := 1, from 1, 6, 7, 8
  have s11 : (d : ℤ) ∣ (b : ℤ) := by first | exact (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := (b : ℤ)) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := (b : ℤ)) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := (b : ℤ)) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := (b : ℤ)) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) (by parley_set_side) (c := (b : ℤ)) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 12. mun:gcd-integer
  have s12a : 0 ≤ (Int.gcd a (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_1 (a := a) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_integer_1 (a := a) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_1 (a := a) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_1 (a := a) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_1 (a := a) (b := (b : ℤ))); parley_set_side)
  have s12b : (Int.gcd a (b : ℤ) : ℤ) ∣ a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := (b : ℤ))); parley_set_side)
  have s12c : (Int.gcd a (b : ℤ) : ℤ) ∣ (b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := (b : ℤ))); parley_set_side)
  -- 13. inequalities, from H2
  have s13 : (b : ℤ) ≠ 0 := by parley_set_side
  -- 14. contradiction
  have s14 : ¬ (a = 0 ∧ (b : ℤ) = 0) := by
    by_contra hc_hS
    have hS : a = 0 ∧ (b : ℤ) = 0 := by parley_suppose hc_hS
    -- 14.1. restate 13
    have s14_1 : (b : ℤ) ≠ 0 := by parley_set_side
    all_goals parley_set_side
  -- 15. mun:gcd-natural, from 14
  have s15 : 0 < (Int.gcd a (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := (b : ℤ)) s14) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := (b : ℤ)) s14)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := (b : ℤ)) s14) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := (b : ℤ)) s14) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := (b : ℤ)) s14); parley_set_side)
  -- 16. thm:divides-gcd, from 10, 11
  have s16 : (d : ℤ) ∣ (Int.gcd a (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (d : ℤ)) (a := a) (b := (b : ℤ)) s10 s11) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (d : ℤ)) (a := a) (b := (b : ℤ)) s10 s11)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (d : ℤ)) (a := a) (b := (b : ℤ)) s10 s11) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (d : ℤ)) (a := a) (b := (b : ℤ)) s10 s11) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (d : ℤ)) (a := a) (b := (b : ℤ)) s10 s11); parley_set_side)
  -- 17. mun:divides-le e := d, m := gcd(a, b), from 6, 15, 16
  have s17 : (d : ℤ) ≤ (Int.gcd a (b : ℤ) : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_set_side) (m := Int.gcd a (b : ℤ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_set_side) (m := Int.gcd a (b : ℤ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_set_side) (m := Int.gcd a (b : ℤ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_set_side) (m := Int.gcd a (b : ℤ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 18. mun:divides-combination e := gcd(a, b), x := x₀, y := y₀, from 12
  have s18 : (Int.gcd a (b : ℤ) : ℤ) ∣ a * x₀ + (b : ℤ) * y₀ := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a (b : ℤ) : ℤ)) (a := a) (b := (b : ℤ)) (x := x₀) (y := y₀) s12b s12c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a (b : ℤ) : ℤ)) (a := a) (b := (b : ℤ)) (x := x₀) (y := y₀) s12b s12c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a (b : ℤ) : ℤ)) (a := a) (b := (b : ℤ)) (x := x₀) (y := y₀) s12b s12c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a (b : ℤ) : ℤ)) (a := a) (b := (b : ℤ)) (x := x₀) (y := y₀) s12b s12c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a (b : ℤ) : ℤ)) (a := a) (b := (b : ℤ)) (x := x₀) (y := y₀) s12b s12c); parley_set_side)
  -- 19. substitute d = a·x₀ + b·y₀ (line 7) into line 18
  have s19 : (Int.gcd a (b : ℤ) : ℤ) ∣ (d : ℤ) := by parley_subst_at s7 s18
  -- 20. mun:divides-le e := gcd(a, b), m := d, from 6, 15, 19
  have s20 : (Int.gcd a (b : ℤ) : ℤ) ≤ (d : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.gcd a (b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.gcd a (b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.gcd a (b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := Int.gcd a (b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 21. antisymmetry, from 17, 20
  have s21 : (d : ℤ) = (Int.gcd a (b : ℤ) : ℤ) := by parley_set_side
  -- 22. transitivity, from 7, 21
  have s22 : a * x₀ + (b : ℤ) * y₀ = (Int.gcd a (b : ℤ) : ℤ) := by parley_set_side
  -- 23. exhibit, from 22
  have s23 : ∃ x : ℤ, ∃ y : ℤ, a * x + (b : ℤ) * y = (Int.gcd a (b : ℤ) : ℤ) := ⟨x₀, y₀, by parley_set_side⟩
  all_goals exact s23

end Parley.Stdlib.Divisibility.Bezout
