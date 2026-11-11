module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.RationalSquaresSumNotThree

set_option maxHeartbeats 800000 in
theorem rational_squares_sum_not_three :
    ¬ (∃ x : ℚ, ∃ y : ℚ, x ^ 2 + y ^ 2 - 3 = 0) := by
  -- the theorem. contradiction
  intro hS
  set T : Set ℤ := {r : ℤ | 0 < r ∧ (∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * r ^ 2)} with hD1
  -- 1. obtain x, y from S
  obtain ⟨x, y, s1⟩ := hS
  -- 2. obtain a, b: mun:rational-coprime
  obtain ⟨a, b, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Numbers.mun_rational_coprime (x := x))
  -- 3. obtain c, d: mun:rational-coprime x := y
  obtain ⟨c, d, s3a, ⟨s3b, s3c⟩⟩ := (Parley.Items.Stdlib.Numbers.mun_rational_coprime (x := y))
  -- 4. substitute x = a/b (line 2) into line 1
  have s4 : ((a : ℚ) / (b : ℚ)) ^ 2 + y ^ 2 - 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℚ => t ^ 2 + y ^ 2 - 3 = 0)) s2b s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. substitute y = c/d (line 3) into line 4
  have s5 : ((a : ℚ) / (b : ℚ)) ^ 2 + ((c : ℚ) / (d : ℚ)) ^ 2 - 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℚ => ((a : ℚ) / (b : ℚ)) ^ 2 + t ^ 2 - 3 = 0)) s3b s4; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. algebra, from 5
  have s6 : (a * d) ^ 2 + (c * b) ^ 2 = 3 * (b * d) ^ 2 := by qify at *; linear_combination (norm := parley_field) ((b : ℚ) ^ 2 * (d : ℚ) ^ 2) * s5
  -- 7. exhibit, from 6
  have s7 : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (b * d) ^ 2 := ⟨a * d, c * b, s6⟩
  -- 8. def:set-builder u := b·d, from D1, 7
  have s8 : b * d ∈ T := by
    have hI : b * d ∈ {t : ℤ | 0 < t ∧ (∃ a : ℤ, ∃ c : ℤ, a ^ 2 + c ^ 2 = 3 * t ^ 2)} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * r ^ 2)) (X := {n : ℤ | 0 < n}) (u := b * d))).mpr (by parley_set_side))
    exact hI
  -- 9. mun:set-builder-subset, from D1
  have s9 : T ⊆ {n : ℤ | 0 < n} := by
    try simp only [hD1] at *
    try push_cast at *
    have hI : {t : ℤ | 0 < t ∧ (∃ a : ℤ, ∃ b : ℤ, a ^ 2 + b ^ 2 = 3 * t ^ 2)} ⊆ {n : ℤ | 0 < n} := by parley_instance ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℤ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * r ^ 2)) (X := {n : ℤ | 0 < n})))
    exact hI
  -- 10. obtain m: axi:well-ordering, from 8, 9
  obtain ⟨m, s10a, s10b⟩ := (Parley.Items.Stdlib.Numbers.axi_well_ordering (S := T) s9 (by parley_set_side))
  -- 11. def:set-builder u := m, from D1, 10
  have s11a : 0 < m := by
    try simp only [hD1] at *
    try push_cast at *
    have hI : 0 < m := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * r ^ 2)) (X := {n : ℤ | 0 < n}) (u := m))).mp (by parley_set_side)).1)
    exact hI
  have s11b : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * m ^ 2 := by
    try simp only [hD1] at *
    try push_cast at *
    have hI : ∃ a : ℤ, ∃ b : ℤ, a ^ 2 + b ^ 2 = 3 * m ^ 2 := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * r ^ 2)) (X := {n : ℤ | 0 < n}) (u := m))).mp (by parley_set_side)).2)
    exact hI
  -- 12. obtain p, q from line 11
  obtain ⟨p, q, s12⟩ := s11b
  -- 13. def:divides d := 3, n := p² + q², from 11, 12
  have s13 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨m ^ 2, s12⟩
  -- 14. thm:three-divides-sum-of-squares, from 13
  have s14 : (3 : ℤ) ∣ p := by exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := p) (q := q) (by parley_set_side))
  -- 15. substitute
  have s15 : (3 : ℤ) ∣ q ^ 2 + p ^ 2 := by
    have c1 : p ^ 2 + q ^ 2 = q ^ 2 + p ^ 2 := by parley_ring
    have row1 : (3 : ℤ) ∣ q ^ 2 + p ^ 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (3 : ℤ) ∣ t)) c1 s13; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 16. thm:three-divides-sum-of-squares p := q, q := p, from 15
  have s16 : (3 : ℤ) ∣ q := by exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares.three_divides_sum_of_squares (p := q) (q := p) (by parley_set_side))
  -- 17. obtain s: def:divides d := 3, n := p, from 14
  obtain ⟨s, s17⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp s14
  -- 18. obtain t: def:divides d := 3, n := q, from 16
  obtain ⟨t, s18⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := q))).mp s16
  -- 19. substitute p = 3s (line 17) into line 12
  have s19 : (3 * s) ^ 2 + q ^ 2 = 3 * m ^ 2 := by (have h := Eq.subst (motive := (fun u : ℤ => u ^ 2 + q ^ 2 = 3 * m ^ 2)) s17 s12; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 20. substitute q = 3t (line 18) into line 19
  have s20 : (3 * s) ^ 2 + (3 * t) ^ 2 = 3 * m ^ 2 := by (have h := Eq.subst (motive := (fun u : ℤ => (3 * s) ^ 2 + u ^ 2 = 3 * m ^ 2)) s18 s19; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 21. algebra, from 11, 20
  have s21 : m ^ 2 = 3 * (s ^ 2 + t ^ 2) := by qify at *; linear_combination (norm := parley_norm) (-(1 / 3 : ℚ)) * s20
  -- 22. def:divides d := 3, n := m², from 11, 21
  have s22 : (3 : ℤ) ∣ m ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := m ^ 2))).mpr ⟨s ^ 2 + t ^ 2, s21⟩
  -- 23. thm:three-divides-square n := m, from 11, 22
  have s23 : (3 : ℤ) ∣ m := by exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := m) (by parley_set_side))
  -- 24. obtain u: def:divides d := 3, n := m, from 11, 23
  obtain ⟨u, s24⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := m))).mp s23
  -- 25. substitute m = 3u (line 24) into line 21
  have s25 : (3 * u) ^ 2 = 3 * (s ^ 2 + t ^ 2) := by (have h := Eq.subst (motive := (fun w : ℤ => w ^ 2 = 3 * (s ^ 2 + t ^ 2))) s24 s21; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 26. algebra, from 25
  have s26 : s ^ 2 + t ^ 2 = 3 * u ^ 2 := by qify at *; linear_combination (norm := parley_norm) (-(1 / 3 : ℚ)) * s25
  -- 27. inequalities, from 11
  have s27 : m > 0 := by parley_order
  -- 28. substitute m = 3u (line 24) into line 27
  have s28 : 3 * u > 0 := by (have h := Eq.subst (motive := (fun w : ℤ => w > 0)) s24 s27; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 29. inequalities
  have s29 : u > 0 := by parley_order
  -- 30. mun:pos-int-nat m := u, from 29
  have s30 : 0 < u := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := u) s29)
  -- 31. exhibit, from 26
  have s31 : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * u ^ 2 := ⟨s, t, s26⟩
  -- 32. def:set-builder, from D1, 30, 31
  have s32 : u ∈ T := by
    have hI : u ∈ {t : ℤ | 0 < t ∧ (∃ a : ℤ, ∃ b : ℤ, a ^ 2 + b ^ 2 = 3 * t ^ 2)} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * r ^ 2)) (X := {n : ℤ | 0 < n}) (u := u))).mpr (by parley_set_side))
    exact hI
  -- 33. instantiate t := u in line 10, from 32
  have s33 : m ≤ u := by exact (s10b u (by parley_set_side))
  -- 34. inequalities
  have s34 : 3 * u > u := by parley_order
  -- 35. substitute m = 3u (line 24) into line 34
  have s35 : m > u := by (have h := Eq.subst (motive := (fun w : ℤ => w > u)) s24.symm s34; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 36. inequalities, from 11, 35
  have s36 : ¬ m ≤ u := by parley_set_side
  exact s36 s33

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.RationalSquaresSumNotThree
