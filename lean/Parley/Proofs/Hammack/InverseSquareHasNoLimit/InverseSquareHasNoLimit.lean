module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/inverse-square-has-no-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.InverseSquareHasNoLimit.InverseSquareHasNoLimit

theorem inverse_square_has_no_limit (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ), f x = 1 / x ^ 2) :
    ¬ (∃ L : ℝ, Filter.Tendsto f (nhdsWithin 0 (((Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) \ {0})) (nhds L)) := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain L from S
  obtain ⟨L, s1⟩ := hS
  -- 2. def:limit-at D := ℝ ∖ {0}, c := 0, from 1
  have r28_1 : (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ)))
  have s2 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ), x ≠ 0 ∧ abs x < δ → abs (f x - L) < ε)) := by simpa only [sub_zero] using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) r28_1 (c := (0 : ℝ)) (L := L))).mp s1
  -- 3. instantiate ε := 1 in line 2
  have r32_1 : (0 : ℤ) < 1 := by parley_arith
  have s3 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ), x ≠ 0 ∧ abs x < δ → abs (f x - L) < 1) := by exact (s2 (1 : ℝ) (by parley_set_side))
  -- 4. obtain p from line 3
  obtain ⟨p, ⟨s4a, s4b⟩⟩ := s3
  -- 5. inequalities
  have s5 : p ≠ 0 := by parley_set_side
  -- 6. mun:quotient-positive x := 2, y := p, from 4
  have r44_1 : (2 : ℤ) > 0 := by parley_arith
  have s6 : 2 / p > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by parley_set_side) s4a)
  -- 7. obtain m: thm:archimedean-natural x := 2/p, from 5
  obtain ⟨m, s7a, s7b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := 2 / p))
  -- 8. inequalities
  have s8 : p > p / 2 := by parley_order
  -- 9. inequalities, from 7
  have s9 : m ≥ 1 := by parley_order
  -- 10. proof
  have s10 : ∀ j : ℤ, 0 < j → j ≥ m → abs ((j : ℝ) ^ 2 - L) < 1 := by
    intro j hK1
    intro hA1
    -- 10.1. inequalities, from K1
    have s10_1 : j > 0 := by parley_order
    -- 10.2. inequalities, from 7
    have s10_2 : m > 0 := by parley_order
    -- 10.3. mun:reciprocal-order x := m, y := j, from A1
    have r72_1 : m > 0 := by parley_set_side
    have r72_2 : j > 0 := by parley_set_side
    have s10_3 : 1 / (j : ℚ) ≤ 1 / (m : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (m : ℚ)) (by exact_mod_cast gt_iff_lt.mp r72_1) (y := (j : ℚ)) (by exact_mod_cast gt_iff_lt.mp r72_2))).mp (by parley_set_side)
    -- 10.4. inequalities
    have r77_1 : p ≠ 0 := by exact s5
    have s10_4 : (m : ℝ) ≥ 2 / p := by parley_order
    -- 10.5. mun:reciprocal-order x := 2/p, y := m, from 10.4
    have r83_1 : 2 / p > 0 := by parley_set_side
    have r83_2 : m > 0 := by parley_set_side
    have r83_3 : p ≠ 0 := by exact s5
    have s10_5 : 1 / (m : ℝ) ≤ 1 / (2 / p) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) r83_1 (y := (m : ℝ)) (by exact_mod_cast gt_iff_lt.mp r83_2))).mp s10_4
    -- 10.6. algebra
    have r89_1 : p ≠ 0 := by exact s5
    have s10_6 : 1 / (2 / p) = p / 2 := by parley_ring
    -- 10.7. transitivity, from 10.3, 10.5, 10.6, 8
    have r93_1 : p ≠ 0 := by exact s5
    have s10_7 : 1 / (j : ℝ) < p := by parley_order
    set t : ℝ := 1 / (j : ℝ) with hD1
    have hD1_kind : True := by parley_set_side
    -- 10.8. mun:reciprocal-positive x := j, from D1, 10.1
    have s10_8 : t > 0 := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (j : ℝ)) (by exact_mod_cast gt_iff_lt.mp s10_1))
    -- 10.9. inequalities
    have s10_9 : t ≠ 0 := by parley_set_side
    -- 10.10. mun:remove-member u := t, from 10.9
    have s10_10 : t ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ) := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (0 : ℝ)) (u := t))).mpr ⟨by parley_set_side, s10_9⟩
    -- 10.11. def:abs x := t
    have r112_1 : t ≥ 0 := by parley_set_side
    have s10_11 : abs t = t := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := t)) (by parley_set_side)
    -- 10.12. transitivity, from D1, 10.7
    have s10_12 : t < p := by parley_order
    -- 10.13. transitivity, from 10.11, 10.12
    have s10_13 : abs t < p := by exact Eq.trans_lt s10_11 s10_12
    -- 10.14. instantiate x := t in line 4, from 10.9, 10.10, 10.13
    have s10_14 : abs (f t - L) < 1 := by exact (s4b t s10_10 (by parley_set_side))
    -- 10.15. instantiate x := t in H2, from 10.10
    have s10_15 : f t = 1 / t ^ 2 := by exact (hH2 t s10_10)
    -- 10.16. algebra, from D1
    have s10_16 : t * (j : ℝ) = 1 := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      parley_ring
    set T : ℝ := t ^ 2 with hD2
    have hD2_kind : True := by parley_set_side
    -- 10.17. mun:square-positive x := t, from D2, 10.9
    have s10_17 : T > 0 := by
      try simp only [hD2] at ⊢
      try push_cast at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_square_positive (x := t) s10_9)
    -- 10.18. algebra, from D2, 10.16
    have s10_18 : (j : ℝ) ^ 2 * T = 1 := by
      try simp only [hD2] at s10_16 ⊢
      try push_cast at s10_16 ⊢
      linear_combination (norm := parley_norm) ((j : ℝ) * t + 1) * s10_16
    -- 10.19. algebra, from 10.18
    have r141_1 : T ≠ 0 := by parley_set_side
    have s10_19 : 1 / T = (j : ℝ) ^ 2 := by linear_combination (norm := parley_field) ((-1) / ((T))) * s10_18
    -- 10.20. substitute t² = T (D2) into line 10.15
    have s10_20 : f t = 1 / T := by (have h := Eq.subst (motive := (fun u : ℝ => f t = 1 / u)) hD2.symm s10_15; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 10.21. transitivity, from 10.20, 10.19
    have s10_21 : f t = (j : ℝ) ^ 2 := by parley_set_side
    -- 10.22. substitute f(t) = j² (line 10.21) into line 10.14
    (have h := Eq.subst (motive := (fun u : ℝ => abs (u - L) < 1)) s10_21 s10_14; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 11. instantiate j := m in line 10
  have r154_1 : m ≥ m := by parley_order
  have s11 : abs ((m : ℝ) ^ 2 - L) < 1 := by exact (s10 m s7a r154_1)
  -- 12. instantiate j := m + 1 in line 10
  have r158_1 : m + 1 ≥ m := by parley_order
  have s12 : abs (((m : ℝ) + 1) ^ 2 - L) < 1 := by exact_mod_cast (s10 (m + 1) (by parley_set_side) r158_1)
  -- 13. mun:abs-difference-lt x := m², c := L, δ := 1, from 11
  have s13 : L - 1 < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 < L + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := (m : ℝ) ^ 2) (c := L) (δ := (1 : ℝ)))).mp s11
  -- 14. mun:abs-difference-lt x := (m + 1)², c := L, δ := 1, from 12
  have s14 : L - 1 < ((m : ℝ) + 1) ^ 2 ∧ ((m : ℝ) + 1) ^ 2 < L + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := ((m : ℝ) + 1) ^ 2) (c := L) (δ := (1 : ℝ)))).mp s12
  -- 15. inequalities, from 13, 14
  have s15 : L - 1 + ((m : ℝ) + 1) ^ 2 < (m : ℝ) ^ 2 + (L + 1) := by parley_order
  -- 16. inequalities
  have s16 : (m + 1) ^ 2 - m ^ 2 < 2 := by parley_order
  -- 17. algebra
  have s17 : (m + 1) ^ 2 - m ^ 2 = 2 * m + 1 := by parley_ring
  -- 18. inequalities
  have s18 : 2 * m + 1 ≥ 3 := by parley_order
  -- 19. transitivity, from 17, 18
  have s19 : (m + 1) ^ 2 - m ^ 2 ≥ 3 := by parley_order
  -- 20. inequalities, from 19
  have s20 : ¬ (m + 1) ^ 2 - m ^ 2 < 2 := by parley_set_side
  exact s20 s16

end Parley.Proofs.Hammack.InverseSquareHasNoLimit.InverseSquareHasNoLimit
