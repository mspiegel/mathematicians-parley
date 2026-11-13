module

public import AlgebraTactics
public import ArithTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/reciprocal-square-no-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalSquareNoLimit.ReciprocalSquareNoLimit

theorem reciprocal_square_no_limit (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), f x = 1 / (x ^ 2 - 2 * x + 1)) :
    ¬ (∃ L : ℝ, Filter.Tendsto f (nhdsWithin 1 (((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) \ {1})) (nhds L)) := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain L from S
  obtain ⟨L, s1⟩ := hS
  -- 2. def:limit-at D := ℝ ∖ {1}, c := 1, from 1
  have r33_1 : (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ)} : Set ℝ)))
  have s2 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), x ≠ 1 ∧ abs (x - 1) < δ → abs (f x - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) r33_1 (c := (1 : ℝ)) (L := L))).mp s1
  -- 3. instantiate ε := 1 in line 2
  have r37_1 : (0 : ℤ) < 1 := by parley_arith
  have s3 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), x ≠ 1 ∧ abs (x - 1) < δ → abs (f x - L) < 1) := by exact (s2 (1 : ℝ) (by norm_num))
  -- 4. obtain p from line 3
  obtain ⟨p, ⟨s4a, s4b⟩⟩ := s3
  -- 5. inequalities
  have s5 : p ≠ 0 := ne_of_gt (by linarith only [s4a])
  -- 6. mun:reciprocal-positive x := p, from 4
  have s6 : 1 / p > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := p) s4a)
  -- 7. mun:quotient-real x := 1, y := p, from 5
  -- 8. mun:max-real x := 1/p, y := L + 1, from 7
  -- 9. obtain N: thm:archimedean-natural x := max(1/p, L + 1), from 8
  obtain ⟨N, s9a, s9b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := max (1 / p) (L + 1)))
  -- 10. mun:le-max x := 1/p, y := L + 1, from 7
  have s10 : 1 / p ≤ max (1 / p) (L + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := 1 / p) (y := L + 1))
  -- 11. mun:le-max x := 1/p, y := L + 1, from 7
  have s11 : L + 1 ≤ max (1 / p) (L + 1) := by exact (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := 1 / p) (y := L + 1))
  -- 12. transitivity, from 10, 9
  have r67_1 : p ≠ 0 := by exact s5
  have s12 : 1 / p < (N : ℝ) := by exact lt_of_le_of_lt s10 s9b
  -- 13. transitivity, from 11, 9
  have s13 : L + 1 < (N : ℝ) := by exact lt_of_le_of_lt s11 s9b
  -- 14. inequalities, from 9
  have s14 : N > 0 := by linarith only [s9a]
  -- 15. mun:reciprocal-positive x := N, from 14
  have s15 : 1 / (N : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp s14))
  -- 16. inequalities
  have s16 : 1 + 1 / (N : ℚ) ≠ 1 := ne_of_gt (by linarith only [s15])
  -- 17. mun:remove-member u := 1 + 1/N, from 16
  have s17 : 1 + 1 / (N : ℝ) ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ) := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (u := 1 + 1 / (N : ℝ)))).mpr ⟨Set.mem_univ _, (show ¬ 1 + 1 / (N : ℝ) = (1 : ℝ) by have h := (Rat.cast_inj (α := ℝ)).not.mpr s16; simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; exact h)⟩
  -- 18. mun:reciprocal-order-strict x := 1/p, y := N, from 6, 7, 12, 14
  have s18 : 1 / (N : ℝ) < 1 / (1 / p) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := 1 / p) s6 (y := (N : ℝ)) (by exact_mod_cast gt_iff_lt.mp s14))).mp s12
  -- 19. substitute
  have r94_1 : p ≠ 0 := by exact s5
  have s19 : 1 / (N : ℝ) < p := by
    have c1 : 1 / (1 / p) = p := by parley_ring
    have row1 : 1 / (N : ℝ) < p := by (have h := Eq.subst (motive := (fun t : ℝ => 1 / (N : ℝ) < t)) c1 s18; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 20. algebra
  have s20 : 1 + 1 / (N : ℚ) - 1 = 1 / (N : ℚ) := by parley_ring
  -- 21. calculation
  have r103_1 : 1 / (N : ℚ) ≥ 0 := by linarith only [s15]
  have s21 : abs (1 + 1 / (N : ℝ) - 1) < p := by
    calc abs (1 + 1 / (N : ℝ) - 1) = abs (1 / (N : ℝ)) := by (have h := congrArg (fun t : ℚ => abs t) s20; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 / (N : ℝ) := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (show 0 ≤ 1 / (N : ℝ) by have h := (Rat.cast_le (K := ℝ)).mpr (ge_iff_le.mp r103_1); simp only [Rat.cast_div, Rat.cast_zero, Rat.cast_one, Rat.cast_intCast] at h; exact h)
      _ < p := by exact s19
  -- 22. join 16, 21
  have s22 : 1 + 1 / (N : ℚ) ≠ 1 ∧ abs (1 + 1 / (N : ℝ) - 1) < p := ⟨s16, s21⟩
  -- 23. instantiate x := 1 + 1/N in line 4, from 17, 22
  have s23 : abs (f (1 + 1 / (N : ℝ)) - L) < 1 := by exact (s4b (1 + 1 / (N : ℝ)) s17 ⟨(show 1 + 1 / (N : ℝ) ≠ 1 by have h := (Rat.cast_inj (α := ℝ)).not.mpr s22.1; simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; exact h), s22.2⟩)
  -- 24. inequalities
  have s24 : 1 / (N : ℚ) ≠ 0 := ne_of_gt (by linarith only [s15])
  -- 25. mun:square-positive x := 1/N, from 24
  have s25 : (1 / (N : ℚ)) ^ 2 > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_positive (x := 1 / (N : ℚ)) s24)
  -- 26. substitute
  have s26 : (1 + 1 / (N : ℚ)) ^ 2 - 2 * (1 + 1 / (N : ℚ)) + 1 > 0 := by
    have c1 : (1 / (N : ℚ)) ^ 2 = (1 + 1 / (N : ℚ)) ^ 2 - 2 * (1 + 1 / (N : ℚ)) + 1 := by parley_ring
    have row1 : (1 + 1 / (N : ℚ)) ^ 2 - 2 * (1 + 1 / (N : ℚ)) + 1 > 0 := by (have h := Eq.subst (motive := (fun t : ℚ => t > 0)) c1 s25; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 27. inequalities
  have s27 : (1 + 1 / (N : ℚ)) ^ 2 - 2 * (1 + 1 / (N : ℚ)) + 1 ≠ 0 := ne_of_gt (by linarith only [s26])
  -- 28. calculation
  have s28 : f (1 + 1 / (N : ℝ)) = (N : ℝ) ^ 2 := by
    calc f (1 + 1 / (N : ℝ)) = 1 / ((1 + 1 / (N : ℝ)) ^ 2 - 2 * (1 + 1 / (N : ℝ)) + 1) := by exact (hH2 (1 + 1 / (N : ℝ)) s17)
      _ = (N : ℝ) ^ 2 := by parley_ring
  -- 29. mun:abs-difference-lt x := f(1 + 1/N), c := L, δ := 1, from 23
  have s29 : L - 1 < f (1 + 1 / (N : ℝ)) ∧ f (1 + 1 / (N : ℝ)) < L + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (1 + 1 / (N : ℝ))) (c := L) (δ := (1 : ℝ)))).mp s23
  -- 30. substitute f(1 + 1/N) = N² (line 28) into line 29
  have s30 : (N : ℝ) ^ 2 < L + 1 := by (have h := Eq.subst (motive := (fun t : ℝ => t < L + 1)) s28 s29.2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 31. mun:multiply-le x := 1, y := N, c := N, from 9
  have s31 : N * 1 ≤ N * N := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := N) (c := N) s9a s9a)
  -- 32. inequalities
  have s32 : N ≤ N ^ 2 := by linarith only [s31]
  -- 33. transitivity, from 13, 32
  have s33 : L + 1 < (N : ℝ) ^ 2 := by exact lt_of_lt_of_le s13 (show (N : ℝ) ≤ (N : ℝ) ^ 2 by exact_mod_cast s32)
  -- 34. inequalities
  have s34 : L + 1 ≤ (N : ℝ) ^ 2 := by linarith only [s33]
  -- 35. inequalities, from 34
  have s35 : ¬ (N : ℝ) ^ 2 < L + 1 := by linarith only [s34]
  exact s35 s30

end Parley.Proofs.Hammack.ReciprocalSquareNoLimit.ReciprocalSquareNoLimit
