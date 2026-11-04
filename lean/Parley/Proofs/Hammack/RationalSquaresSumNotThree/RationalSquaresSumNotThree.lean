module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.RationalSquaresSumNotThree

set_option maxHeartbeats 400000 in
theorem rational_squares_sum_not_three :
    ¬ (∃ x : ℚ, ∃ y : ℚ, x ^ 2 + y ^ 2 - 3 = 0) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ x : ℚ, ∃ y : ℚ, x ^ 2 + y ^ 2 - 3 = 0) := by
    by_contra hc_hS
    have hS : ∃ x : ℚ, ∃ y : ℚ, x ^ 2 + y ^ 2 - 3 = 0 := by parley_suppose hc_hS
    set T : Set ℕ := {r : ℕ | 0 < r ∧ (∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)} with hD1
    -- 1. obtain x, y from S
    obtain ⟨x, y, s1⟩ := hS
    -- 2. obtain a, b: mun:rational-coprime
    obtain ⟨a, b, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Numbers.mun_rational_coprime (x := x))
    -- 3. obtain c, d: mun:rational-coprime x := y
    obtain ⟨c, d, s3a, ⟨s3b, s3c⟩⟩ := (Parley.Items.Stdlib.Numbers.mun_rational_coprime (x := y))
    -- 4. substitute x = a/b (line 2) into line 1
    have s4 : ((a : ℚ) / (b : ℚ)) ^ 2 + y ^ 2 - 3 = 0 := by parley_subst_at s2b s1
    -- 5. substitute y = c/d (line 3) into line 4
    have s5 : ((a : ℚ) / (b : ℚ)) ^ 2 + ((c : ℚ) / (d : ℚ)) ^ 2 - 3 = 0 := by parley_subst_at s3b s4
    -- 6. algebra, from 5
    have s6 : (a * (d : ℤ)) ^ 2 + (c * (b : ℤ)) ^ 2 = 3 * ((b : ℤ) * (d : ℤ)) ^ 2 := by qify at *; linear_combination (norm := parley_field) ((b : ℚ) ^ 2 * (d : ℚ) ^ 2) * s5
    -- 7. exhibit, from 6
    have s7 : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * ((b : ℤ) * (d : ℤ)) ^ 2 := ⟨a * (d : ℤ), c * (b : ℤ), by parley_set_side⟩
    -- 8. def:set-builder u := b·d, from D1, 7
    have s8 : b * d ∈ T := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := b * d))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := b * d))).mpr (by parley_set_side); parley_set_side)
    -- 9. mun:set-builder-subset, from D1
    have s9 : T ⊆ {n : ℕ | 0 < n} := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n})) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n})) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n})); parley_set_side)
    -- 10. obtain m: axi:well-ordering, from 8, 9
    obtain ⟨m, s10a, s10b⟩ := (Parley.Items.Stdlib.Numbers.axi_well_ordering (S := T) s9 (by parley_set_side))
    -- 11. def:set-builder u := m, from D1, 10
    have s11a : 0 < m := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).1; parley_set_side)
    have s11b : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (m : ℤ) ^ 2 := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := m))).mp (by parley_set_side)).2; parley_set_side)
    -- 12. obtain p, q from line 11
    obtain ⟨p, q, s12⟩ := s11b
    -- 13. def:divides d := 3, n := p² + q², from 11, 12
    have s13 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨(m : ℤ) ^ 2, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨(m : ℤ) ^ 2, by parley_set_side⟩; parley_set_side)
    -- 14. thm:three-divides-sum-of-squares, from 13
    have s14 : (3 : ℤ) ∣ p := by first | exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := p) (q := q) s13) | exact ((Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := p) (q := q) s13)).symm | simpa using (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := p) (q := q) s13) | exact_mod_cast (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := p) (q := q) s13) | (have h := (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := p) (q := q) s13); parley_set_side)
    -- 15. substitute
    have s15 : (3 : ℤ) ∣ q ^ 2 + p ^ 2 := by
      have c1 : p ^ 2 + q ^ 2 = q ^ 2 + p ^ 2 := by parley_ring
      have row1 : (3 : ℤ) ∣ q ^ 2 + p ^ 2 := by parley_subst_at c1 s13
      exact row1
    -- 16. thm:three-divides-sum-of-squares p := q, q := p, from 15
    have s16 : (3 : ℤ) ∣ q := by first | exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := q) (q := p) s15) | exact ((Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := q) (q := p) s15)).symm | simpa using (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := q) (q := p) s15) | exact_mod_cast (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := q) (q := p) s15) | (have h := (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := q) (q := p) s15); parley_set_side)
    -- 17. obtain s: def:divides d := 3, n := p, from 14
    obtain ⟨s, s17⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_set_side)
    -- 18. obtain t: def:divides d := 3, n := q, from 16
    obtain ⟨t, s18⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := q))).mp (by parley_set_side)
    -- 19. substitute p = 3s (line 17) into line 12
    have s19 : (3 * s) ^ 2 + q ^ 2 = 3 * (m : ℤ) ^ 2 := by parley_subst_at s17 s12
    -- 20. substitute q = 3t (line 18) into line 19
    have s20 : (3 * s) ^ 2 + (3 * t) ^ 2 = 3 * (m : ℤ) ^ 2 := by parley_subst_at s18 s19
    -- 21. algebra, from 11, 20
    have s21 : (m : ℤ) ^ 2 = 3 * (s ^ 2 + t ^ 2) := by qify at *; linear_combination (norm := parley_norm) (-(1 / 3 : ℚ)) * s20
    -- 22. def:divides d := 3, n := m², from 11, 21
    have s22 : (3 : ℤ) ∣ (m : ℤ) ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (m : ℤ) ^ 2))).mpr ⟨s ^ 2 + t ^ 2, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (m : ℤ) ^ 2))).mpr ⟨s ^ 2 + t ^ 2, by parley_set_side⟩; parley_set_side)
    -- 23. thm:three-divides-square n := m, from 11, 22
    have s23 : (3 : ℤ) ∣ (m : ℤ) := by first | exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := (m : ℤ)) s22) | exact ((Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := (m : ℤ)) s22)).symm | simpa using (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := (m : ℤ)) s22) | exact_mod_cast (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := (m : ℤ)) s22) | (have h := (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := (m : ℤ)) s22); parley_set_side)
    -- 24. obtain u: def:divides d := 3, n := m, from 11, 23
    obtain ⟨u, s24⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (m : ℤ)))).mp (by parley_set_side)
    -- 25. substitute m = 3u (line 24) into line 21
    have s25 : (3 * u) ^ 2 = 3 * (s ^ 2 + t ^ 2) := by parley_subst_at s24 s21
    -- 26. algebra, from 25
    have s26 : s ^ 2 + t ^ 2 = 3 * u ^ 2 := by qify at *; linear_combination (norm := parley_norm) (-(1 / 3 : ℚ)) * s25
    -- 27. inequalities, from 11
    have s27 : (m : ℤ) > 0 := by parley_order
    -- 28. substitute m = 3u (line 24) into line 27
    have s28 : 3 * u > 0 := by parley_subst_at s24 s27
    -- 29. inequalities
    have s29 : u > 0 := by parley_order
    -- 30. mun:pos-int-nat m := u, from 29
    have s30 : 0 < u := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := u) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := u) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := u) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := u) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := u) (by parley_set_side)); parley_set_side)
    lift u to ℕ using s30.le
    -- 31. exhibit, from 26
    have s31 : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (u : ℤ) ^ 2 := ⟨s, t, by parley_set_side⟩
    -- 32. def:set-builder, from D1, 30, 31
    have s32 : u ∈ T := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℕ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (r : ℤ) ^ 2)) (X := {n : ℕ | 0 < n}) (u := u))).mpr (by parley_set_side); parley_set_side)
    -- 33. instantiate t := u in line 10, from 32
    have s33 : (m : ℤ) ≤ (u : ℤ) := by first | linarith [(s10b u (by parley_set_side))] | (have h := (s10b u (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s10b u (by parley_set_side)) | (have h := (s10b u (by parley_set_side)); parley_set_side)
    -- 34. inequalities
    have s34 : 3 * (u : ℤ) > (u : ℤ) := by parley_order
    -- 35. substitute m = 3u (line 24) into line 34
    have s35 : (m : ℤ) > (u : ℤ) := by parley_subst_at s24 s34
    -- 36. inequalities, from 11, 35
    have s36 : ¬ (m : ℤ) ≤ (u : ℤ) := by parley_set_side
    all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.RationalSquaresSumNotThree
