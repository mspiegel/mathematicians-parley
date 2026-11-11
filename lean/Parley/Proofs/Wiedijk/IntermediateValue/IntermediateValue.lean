module

public import InstanceTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/wiedijk/intermediate-value.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.IntermediateValue.IntermediateValue

theorem intermediate_value (a : ℝ) (b : ℝ) (hH3 : a < b) (f : ℝ → ℝ) (hH4 : Set.MapsTo f (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (hH6 : f a < 0) (hH7 : 0 < f b) :
    (∃ c ∈ (Set.Icc a b : Set ℝ), f c = 0) := by
  set S : Set ℝ := {x ∈ (Set.Icc a b : Set ℝ) | f x < 0} with hD1
  -- 1. def:interval x := a
  have r37_1 : a ≤ a := by parley_order
  have r37_2 : a ≤ b := by parley_set_side
  have s1 : a ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr ⟨⟨by parley_set_side, r37_1⟩, r37_2⟩
  -- 2. def:set-builder u := a, from D1, H6, 1
  have s2 : a ∈ S := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => f x < 0)) (X := (Set.Icc a b : Set ℝ)) (u := a))).mpr ⟨s1, hH6⟩
  -- 3. mun:set-builder-subset, from D1
  have s3 : S ⊆ (Set.Icc a b : Set ℝ) := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun x : ℝ => f x < 0)) (X := (Set.Icc a b : Set ℝ)))
  -- 4. mun:interval-real
  have s4 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  -- 5. mun:subset-transitive X := S, Y := [a, b], Z := ℝ, from 3, 4
  have s5 : S ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := (Set.Icc a b : Set ℝ)) (Z := (Set.univ : Set ℝ)) s3 (by parley_whole_side))
  -- 6. proof
  have s6 : ∀ s ∈ S, s ≤ b := by
    intro s hK1
    -- 6.1. def:set-builder, from D1, K1
    have s6_1 : s ∈ (Set.Icc a b : Set ℝ) := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => f x < 0)) (X := (Set.Icc a b : Set ℝ)) (u := s))).mp hK1).1
    -- 6.2. def:interval, from 6.1
    exact (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := a) (b := b))).mp s6_1).2
  -- 7. def:upper-bound, from 6
  have s7 : ∀ s ∈ S, s ≤ b := by parley_set_side
  -- 8. obtain c: axi:completeness, from 2, 5, 7
  obtain ⟨c, s8⟩ := (Parley.Items.Stdlib.Calculus.axi_completeness (S := S) s5 (by parley_set_side) (by parley_set_side))
  -- 9. def:least-upper-bound, from 8
  have s9a : ∀ s ∈ S, s ≤ c := by parley_set_side
  have s9b : ∀ u : ℝ, (∀ s ∈ S, s ≤ u) → c ≤ u := by parley_set_side
  -- 10. def:upper-bound, from 9
  have s10 : ∀ s ∈ S, s ≤ c := by parley_set_side
  -- 11. instantiate s := a in line 10, from 2
  have s11 : a ≤ c := by exact (s10 a s2)
  -- 12. instantiate u := b in line 9, from 7
  have s12 : c ≤ b := by exact (s9b b s7)
  -- 13. def:interval x := c, from 11, 12
  have s13 : c ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := c) (a := a) (b := b))).mpr ⟨⟨by parley_set_side, s11⟩, s12⟩
  -- 14. axi:trichotomy x := f(c), from H4, 13
  have s14 : (f c < 0 ∨ f c = 0) ∨ 0 < f c := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := f c))
  -- 15. def:continuous-on, from H5
  have r89_1 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  have s15 : ∀ c' ∈ (Set.Icc a b : Set ℝ), ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Icc a b : Set ℝ), abs (x - c') < δ → abs (f x - f c') < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := (Set.Icc a b : Set ℝ)) r89_1)).mp hH5
  -- 16. cases, from 14
  have s16 : f c = 0 := by
    rcases s14 with (hC1 | hC2) | hC3
    · skip
      -- 16.1. contradiction
      have s16_1 : c ≠ b := by
        intro hS1
        -- 16.1.1. substitute c = b (S1) into C1
        have s16_1_1 : f b < 0 := by (have h := Eq.subst (motive := (fun t : ℝ => f t < 0)) hS1 hC1; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 16.1.2. def:interval x := b
        have r108_1 : a ≤ b := by parley_set_side
        have r108_2 : b ≤ b := by parley_order
        have s16_1_2 : b ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr ⟨⟨by parley_set_side, r108_1⟩, r108_2⟩
        -- 16.1.3. inequalities
        have s16_1_3 : 0 ≤ f b := by parley_order
        -- 16.1.4. inequalities, from 16.1.3
        have s16_1_4 : ¬ f b < 0 := by parley_set_side
        exact s16_1_4 s16_1_1
      -- 16.2. inequalities, from 12, 16.1
      have s16_2 : c < b := by parley_order
      -- 16.3. inequalities
      have s16_3 : -f c > 0 := by parley_order
      -- 16.4. instantiate c′ := c, ε := −f(c) in line 15, from H4, 13, 16.3
      have s16_4 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Icc a b : Set ℝ), abs (x - c) < δ → abs (f x - f c) < -f c) := by exact (s15 c s13 (-f c) s16_3)
      -- 16.5. obtain δ from line 16.4
      obtain ⟨δ, ⟨s16_5a, s16_5b⟩⟩ := s16_4
      set x₁ : ℝ := min b (c + δ / 2) with hD2
      have hD2_kind : True := by trivial
      -- 16.6. inequalities
      have s16_6 : δ / 2 > 0 := by parley_order
      -- 16.7. inequalities
      have s16_7 : c < c + δ / 2 := by parley_order
      -- 16.8. mun:lt-min z := c, x := b, y := c + δ/2, from D2, 16.2, 16.7
      have s16_8 : c < x₁ := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := c) (x := b) (y := c + δ / 2))).mpr ⟨s16_2, s16_7⟩
      -- 16.9. mun:min-le x := b, y := c + δ/2, from D2
      have s16_9a : x₁ ≤ b := by
        try simp only [hD2] at ⊢
        try push_cast at ⊢
        exact (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := b) (y := c + δ / 2))
      have s16_9b : x₁ ≤ c + δ / 2 := by
        try simp only [hD2] at ⊢
        try push_cast at ⊢
        exact (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := b) (y := c + δ / 2))
      -- 16.10. inequalities
      have s16_10 : x₁ - c ≤ δ / 2 := by parley_order
      -- 16.11. inequalities
      have s16_11 : δ / 2 < δ := by parley_order
      -- 16.12. transitivity, from 16.10, 16.11
      have s16_12 : x₁ - c < δ := by parley_order
      -- 16.13. transitivity, from 11, 16.8
      have s16_13 : a < x₁ := by parley_order
      -- 16.14. inequalities
      have s16_14 : a ≤ x₁ := by parley_order
      -- 16.15. def:interval x := x₁, from 16.9, 16.14
      have s16_15 : x₁ ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := x₁) (a := a) (b := b))).mpr ⟨⟨by parley_set_side, s16_14⟩, s16_9a⟩
      -- 16.16. inequalities
      have s16_16 : c - δ < c := by parley_order
      -- 16.17. transitivity, from 16.16, 16.8
      have s16_17 : c - δ < x₁ := by parley_order
      -- 16.18. inequalities
      have s16_18 : x₁ < c + δ := by parley_order
      -- 16.19. mun:abs-difference-lt x := x₁, from 16.17, 16.18
      have s16_19 : abs (x₁ - c) < δ := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x₁) (c := c) (δ := δ))).mpr ⟨s16_17, s16_18⟩
      -- 16.20. instantiate x := x₁ in line 16.5, from 16.15, 16.19
      have s16_20 : abs (f x₁ - f c) < -f c := by exact (s16_5b x₁ s16_15 s16_19)
      -- 16.21. thm:abs-bounds x := f(x₁) − f(c)
      have s16_21 : f x₁ - f c ≤ abs (f x₁ - f c) := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := f x₁ - f c)).1
      -- 16.22. transitivity, from 16.21, 16.20
      have s16_22 : f x₁ - f c < -f c := by parley_order
      -- 16.23. inequalities
      have s16_23 : f x₁ < 0 := by parley_order
      -- 16.24. def:set-builder u := x₁, from D1, 16.15, 16.23
      have s16_24 : x₁ ∈ S := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => f x < 0)) (X := (Set.Icc a b : Set ℝ)) (u := x₁))).mpr ⟨s16_15, s16_23⟩
      -- 16.25. instantiate s := x₁ in line 10, from 16.24
      have s16_25 : x₁ ≤ c := by exact (s10 x₁ s16_24)
      -- 16.26. inequalities, from 16.8
      have s16_26 : ¬ x₁ ≤ c := by parley_set_side
      exact absurd s16_25 s16_26
    · skip
      exact hC2
    · skip
      -- 16.27. instantiate c′ := c, ε := f(c) in line 15, from C3, H4, 13
      have s16_27 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Icc a b : Set ℝ), abs (x - c) < δ → abs (f x - f c) < f c) := by exact (s15 c s13 (f c) hC3)
      -- 16.28. obtain δ from line 16.27
      obtain ⟨δ, ⟨s16_28a, s16_28b⟩⟩ := s16_27
      -- 16.29. proof
      have s16_29 : ∀ s ∈ S, s ≤ c - δ := by
        intro s hK2
        by_contra hS2
        -- 16.29.1. def:set-builder, from D1, K2
        have s16_29_1 : s ∈ (Set.Icc a b : Set ℝ) := by
          try simp only [hD1] at ⊢
          try push_cast at ⊢
          exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => f x < 0)) (X := (Set.Icc a b : Set ℝ)) (u := s))).mp hK2).1
        -- 16.29.2. def:set-builder, from D1, K2
        have s16_29_2 : f s < 0 := by
          try simp only [hD1] at ⊢
          try push_cast at ⊢
          have hI : f s < 0 := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => f x < 0)) (X := (Set.Icc a b : Set ℝ)) (u := s))).mp hK2).2)
          exact hI
        -- 16.29.3. inequalities, from S2
        have s16_29_3 : c - δ < s := by parley_order
        -- 16.29.4. inequalities, from 10, 16.28
        have s16_29_4 : s < c + δ := by have := (s10 s hK2); parley_order
        -- 16.29.5. mun:abs-difference-lt x := s, from 16.29.3, 16.29.4
        have s16_29_5 : abs (s - c) < δ := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := s) (c := c) (δ := δ))).mpr ⟨s16_29_3, s16_29_4⟩
        -- 16.29.6. instantiate x := s in line 16.28, from 16.29.1, 16.29.5
        have s16_29_6 : abs (f s - f c) < f c := by exact (s16_28b s s16_29_1 s16_29_5)
        -- 16.29.7. thm:abs-bounds x := f(s) − f(c)
        have s16_29_7 : -(f s - f c) ≤ abs (f s - f c) := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := f s - f c)).2
        -- 16.29.8. transitivity, from 16.29.7, 16.29.6
        have s16_29_8 : -(f s - f c) < f c := by parley_order
        -- 16.29.9. inequalities
        have s16_29_9 : 0 ≤ f s := by parley_order
        -- 16.29.10. inequalities, from 16.29.9
        have s16_29_10 : ¬ f s < 0 := by parley_set_side
        exact s16_29_10 s16_29_2
      -- 16.30. def:upper-bound, from 16.29
      have s16_30 : ∀ s ∈ S, s ≤ c - δ := by parley_set_side
      -- 16.31. instantiate u := c − δ in line 9, from 16.30
      have s16_31 : c ≤ c - δ := by exact (s9b (c - δ) s16_30)
      -- 16.32. inequalities
      have s16_32 : c - δ < c := by parley_order
      -- 16.33. inequalities, from 16.32
      have s16_33 : ¬ c ≤ c - δ := by parley_set_side
      exact absurd s16_31 s16_33
  -- 17. exhibit, from 13, 16
  exact ⟨c, s13, s16⟩

end Parley.Proofs.Wiedijk.IntermediateValue.IntermediateValue
