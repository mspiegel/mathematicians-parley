module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides

/-! Written from proofs/wiedijk/bezout.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Bezout.Bezout

set_option maxHeartbeats 600000 in
theorem bezout (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) :
    (∃ x : ℤ, ∃ y : ℤ, a * x + b * y = (Int.gcd a b : ℤ)) := by
  set S : Set ℤ := {t : ℤ | 0 < t ∧ (∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)} with hD1
  -- 1. algebra
  have s1 : a = a * 1 + b * 0 := by parley_ring
  -- 2. def:set-builder u := a, from D1, 1
  have s2 : a ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := a))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := a))).mpr (by parley_set_side); parley_set_side)
  -- 3. mun:set-builder-subset, from D1
  have s3 : S ⊆ {n : ℤ | 0 < n} := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n})) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n})) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n})); parley_set_side)
  -- 4. obtain d: axi:well-ordering, from 2, 3
  obtain ⟨d, s4a, s4b⟩ := (Parley.Items.Stdlib.Numbers.axi_well_ordering (S := S) s3 (by parley_set_side))
  -- 5. def:subset, from 3
  have s5 : ∀ t ∈ S, 0 < t := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp (by parley_set_side); parley_set_side)
  -- 6. instantiate t := d in line 5, from 4
  have s6 : 0 < d := by first | exact (s5 d (by parley_set_side)) | exact ((s5 d (by parley_set_side))).symm | simpa using (s5 d (by parley_set_side)) | exact_mod_cast (s5 d (by parley_set_side)) | (have h := (s5 d (by parley_set_side)); parley_set_side)
  -- 7. obtain x₀, y₀: def:set-builder u := d, from D1, 4
  obtain ⟨_, x₀, y₀, s7⟩ := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := d))).mp (by parley_set_side)
  -- 8. proof
  have s8 : ∀ x : ℤ, ∀ y : ℤ, 0 < a * x + b * y → d ≤ a * x + b * y := by
    intro x
    intro y
    intro hK3
    -- 8.1. def:set-builder u := a·x + b·y, from D1, K3
    have s8_1 : a * x + b * y ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := a * x + b * y))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := a * x + b * y))).mpr (by parley_set_side); parley_set_side)
    -- 8.2. instantiate s := a·x + b·y in line 4, from 8.1
    have s8_2 : d ≤ a * x + b * y := by first | linarith [(s4b (a * x + b * y) (by parley_set_side))] | (have h := (s4b (a * x + b * y) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4b (a * x + b * y) (by parley_set_side)) | (have h := (s4b (a * x + b * y) (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  -- 9. algebra
  have s9 : a = a * 1 + b * 0 := by parley_ring
  -- 10. thm:least-combination-divides c := a, u := 1, v := 0, from 6, 7, 8, 9
  have s10 : d ∣ a := by first | exact (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := a) (by parley_set_side) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 s8) | exact ((Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := a) (by parley_set_side) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 s8)).symm | simpa using (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := a) (by parley_set_side) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 s8) | exact_mod_cast (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := a) (by parley_set_side) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 s8) | (have h := (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := a) (by parley_set_side) (d := d) (by parley_set_side) (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 s8); parley_set_side)
  -- 11. algebra
  have s11 : b = a * 0 + b * 1 := by parley_ring
  -- 12. thm:least-combination-divides c := b, u := 0, v := 1, from 6, 7, 8, 11
  have s12 : d ∣ b := by first | exact (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := b) (by parley_set_side) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s11 s7 s8) | exact ((Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := b) (by parley_set_side) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s11 s7 s8)).symm | simpa using (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := b) (by parley_set_side) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s11 s7 s8) | exact_mod_cast (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := b) (by parley_set_side) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s11 s7 s8) | (have h := (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) (by parley_set_side) (b := b) (by parley_set_side) (c := b) (by parley_set_side) (d := d) (by parley_set_side) (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s11 s7 s8); parley_set_side)
  -- 13. def:gcd
  have s13a : 0 < (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_set_side) (b := b) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_set_side) (b := b) (by parley_set_side)); parley_set_side)
  have s13b : (Int.gcd a b : ℤ) ∣ a := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_set_side) (b := b) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_set_side) (b := b) (by parley_set_side)); parley_set_side)
  have s13c : (Int.gcd a b : ℤ) ∣ b := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_set_side) (b := b) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_set_side) (b := b) (by parley_set_side)); parley_set_side)
  have s13d : ∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_set_side) (b := b) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_set_side) (b := b) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_set_side) (b := b) (by parley_set_side)); parley_set_side)
  -- 14. instantiate e := d in line 13, from 6, 10, 12
  have s14 : d ≤ (Int.gcd a b : ℤ) := by first | linarith [(s13d d (by parley_set_side) (by parley_set_side))] | (have h := (s13d d (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s13d d (by parley_set_side) (by parley_set_side)) | (have h := (s13d d (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 15. mun:divides-combination e := gcd(a, b), x := x₀, y := y₀, from 13
  have s15 : (Int.gcd a b : ℤ) ∣ a * x₀ + b * y₀ := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s13b s13c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s13b s13c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s13b s13c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s13b s13c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s13b s13c); parley_set_side)
  -- 16. substitute d = a·x₀ + b·y₀ (line 7) into line 15
  have s16 : (Int.gcd a b : ℤ) ∣ d := by parley_subst_at s7 s15
  -- 17. mun:divides-le e := gcd(a, b), m := d, from 6, 13, 16
  have s17 : (Int.gcd a b : ℤ) ≤ d := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) s16)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) s16); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) s16) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) (by parley_set_side) (m := d) (by parley_set_side) s16); parley_set_side)
  -- 18. antisymmetry, from 14, 17
  have s18 : d = (Int.gcd a b : ℤ) := by parley_set_side
  -- 19. calculation
  have s19 : a * x₀ + b * y₀ = (Int.gcd a b : ℤ) := by
    calc a * x₀ + b * y₀ = d := by parley_set_side
      _ = (Int.gcd a b : ℤ) := by parley_set_side
  -- 20. exhibit, from 19
  have s20 : ∃ x : ℤ, ∃ y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) := ⟨x₀, y₀, by parley_set_side⟩
  all_goals exact s20

end Parley.Proofs.Wiedijk.Bezout.Bezout
