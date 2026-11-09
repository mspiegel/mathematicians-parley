module

public import ArithTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-map-over-a-set-binding-its-letter.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapOverASetBindingItsLetter.AMapOverASetBindingItsLetter

set_option maxHeartbeats 1200000 in
theorem a_map_over_a_set_binding_its_letter (g : ℝ → ℝ) (hD2 : ∀ x : ℝ, x ∈ {x : ℝ | x > 0} → g x = Real.sqrt x) :
    ContinuousOn g {x : ℝ | x > 0} := by
  set D : Set ℝ := {x : ℝ | x > 0} with hD1
  -- 1. mun:set-builder-subset, from D1
  have s1 : D ⊆ (Set.univ : Set ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    have hI : {t : ℝ | 0 < t} ⊆ (Set.univ : Set ℝ) := by parley_instance ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun x : ℝ => 0 < x)) (X := (Set.univ : Set ℝ))))
    exact hI
  -- 2. proof
  have s2 : ∀ x ∈ D, True := by
    intro x hK1
    -- 2.1. def:set-builder, from D1, K1
    have s2_1 : x > 0 := by
      try simp only [hD1] at *
      try push_cast at *
      have hI : 0 < x := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => 0 < x)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2)
      exact hI
    -- 2.2. inequalities
    have s2_2 : x ≥ 0 := by parley_order
    -- 2.3. def:sqrt, from 2.1, 2.2
    have s2_3a : Real.sqrt x ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) s2_2)
    have s2_3b : Real.sqrt x ^ 2 = x := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) s2_2)
    -- 2.4. D2, from K1
    have s2_4 : g x = Real.sqrt x := by (try simp only [hD2]); first | done | parley_set_side
    -- 2.5. substitute g(x) = √x (line 2.4) into line 2.3
    exact trivial
  -- 3. mun:function-into, from 2
  have s3 : Set.MapsTo g D (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := D) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 4. proof
  have s4 : ∀ c ∈ D, ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - c) < δ → abs (g x - g c) < ε)) := by
    intro c hK2
    intro ε
    intro hA1
    -- 4.1. def:set-builder, from D1, K2
    have s4_1 : c > 0 := by
      try simp only [hD1] at *
      try push_cast at *
      have hI : 0 < c := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => 0 < x)) (X := (Set.univ : Set ℝ)) (u := c))).mp (by parley_set_side)).2)
      exact hI
    -- 4.2. inequalities
    have s4_2 : c ≥ 0 := by parley_order
    -- 4.3. def:sqrt x := c, from 4.1, 4.2
    have s4_3a : Real.sqrt c ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := c) s4_2)
    have s4_3b : Real.sqrt c ^ 2 = c := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := c) s4_2)
    -- 4.4. contradiction
    have s4_4 : Real.sqrt c > 0 := by
      by_contra hS1
      -- 4.4.1. inequalities, from S1
      have s4_4_1 : Real.sqrt c ≤ 0 := by parley_order
      -- 4.4.2. inequalities, from 4.3
      have s4_4_2 : Real.sqrt c ≥ 0 := by parley_order
      -- 4.4.3. antisymmetry, from 4.4.1, 4.4.2
      have s4_4_3 : Real.sqrt c = 0 := by parley_set_side
      -- 4.4.4. substitute √c = 0 (line 4.4.3)
      have s4_4_4 : Real.sqrt c ^ 2 = 0 ^ 2 := by parley_subst s4_4_3
      -- 4.4.5. arithmetic
      have s4_4_5 : (0 ^ 2 : ℤ) = 0 := by parley_arith
      -- 4.4.6. calculation
      have s4_4_6 : c = 0 := by
        calc c = Real.sqrt c ^ 2 := by exact s4_3b.symm
          _ = 0 ^ 2 := by exact s4_4_4
          _ = 0 := by parley_set_side
      -- 4.4.7. inequalities
      have s4_4_7 : c ≤ 0 := by parley_order
      -- 4.4.8. inequalities, from 4.4.7
      have s4_4_8 : ¬ c > 0 := by parley_set_side
      exact s4_4_8 s4_1
    -- 4.5. mun:less-scaled x := 0, y := √c, c := ε, from A1, 4.3, 4.4
    have s4_5 : ε * 0 < ε * Real.sqrt c := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := Real.sqrt c) (c := ε) (by parley_set_side))).mp s4_4
    -- 4.6. membership, from 4.3
    -- 4.7. inequalities, from 4.3, 4.5
    have s4_7 : ε * Real.sqrt c > 0 := by parley_order
    -- 4.8. proof
    have s4_8 : ∀ x ∈ D, abs (x - c) < ε * Real.sqrt c → abs (g x - g c) < ε := by
      intro x hK4
      intro hA2
      -- 4.8.1. def:set-builder, from D1, K4
      have s4_8_1 : x > 0 := by
        try simp only [hD1] at *
        try push_cast at *
        have hI : 0 < x := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => 0 < x)) (X := (Set.univ : Set ℝ)) (u := x))).mp (by parley_set_side)).2)
        exact hI
      -- 4.8.2. inequalities
      have s4_8_2 : x ≥ 0 := by parley_order
      -- 4.8.3. def:sqrt, from 4.8.1, 4.8.2
      have s4_8_3a : Real.sqrt x ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) s4_8_2)
      have s4_8_3b : Real.sqrt x ^ 2 = x := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) s4_8_2)
      -- 4.8.4. membership, from 4.1, 4.8.1
      -- 4.8.5. mun:abs-real x := x − c, from 4.8.4
      -- 4.8.6. membership, from 4.3, 4.8.3
      -- 4.8.7. mun:abs-real x := √x − √c, from 4.8.6
      -- 4.8.8. D2, from K4
      have s4_8_8 : g x = Real.sqrt x := by (try simp only [hD2]); first | done | parley_set_side
      -- 4.8.9. D2, from K2
      have s4_8_9 : g c = Real.sqrt c := by (try simp only [hD2]); first | done | parley_set_side
      -- 4.8.10. algebra, from 4.3, 4.8.3
      have s4_8_10 : (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) = x - c := by linear_combination (norm := parley_norm) (-1) * s4_3b + s4_8_3b
      -- 4.8.11. inequalities, from 4.3, 4.8.3
      have s4_8_11 : Real.sqrt x + Real.sqrt c ≥ 0 := by parley_order
      -- 4.8.12. mun:abs-nonneg x := √x − √c, from 4.8.6
      have s4_8_12 : abs (Real.sqrt x - Real.sqrt c) ≥ 0 := by
        have hI : 0 ≤ abs (Real.sqrt x - Real.sqrt c) := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (Real.sqrt x : ℂ) - (Real.sqrt c : ℂ))))
        exact hI
      -- 4.8.13. def:abs x := √x + √c, from 4.8.11
      have s4_8_13 : abs (Real.sqrt x + Real.sqrt c) = Real.sqrt x + Real.sqrt c := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Real.sqrt x + Real.sqrt c)) s4_8_11
      -- 4.8.14. substitute (√x − √c)·(√x + √c) = x − c (line 4.8.10)
      have s4_8_14 : abs (x - c) = abs ((Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c)) := by parley_subst s4_8_10
      -- 4.8.15. mun:abs-product x := √x − √c, y := √x + √c, from 4.8.6
      have s4_8_15 : abs ((Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c)) = abs (Real.sqrt x - Real.sqrt c) * abs (Real.sqrt x + Real.sqrt c) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := Real.sqrt x - Real.sqrt c) (y := Real.sqrt x + Real.sqrt c))
      -- 4.8.16. substitute |√x + √c| = √x + √c (line 4.8.13)
      have s4_8_16 : abs (Real.sqrt x - Real.sqrt c) * abs (Real.sqrt x + Real.sqrt c) = abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) := by parley_subst s4_8_13
      -- 4.8.17. calculation
      have s4_8_17 : abs (x - c) = abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) := by
        calc abs (x - c) = abs ((Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c)) := by exact s4_8_14
          _ = abs (Real.sqrt x - Real.sqrt c) * abs (Real.sqrt x + Real.sqrt c) := by exact s4_8_15
          _ = abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) := by exact s4_8_16
      -- 4.8.18. mun:product-nonneg x := |√x − √c|, y := √x, from 4.8.3, 4.8.7, 4.8.12
      have s4_8_18 : abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := abs (Real.sqrt x - Real.sqrt c)) (y := Real.sqrt x) (by parley_set_side) (by parley_set_side))
      -- 4.8.19. algebra, from 4.3, 4.8.3
      have s4_8_19 : abs (Real.sqrt x - Real.sqrt c) * (Real.sqrt x + Real.sqrt c) = abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x + Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) := by linear_combination (norm := parley_norm) 0
      -- 4.8.20. transitivity, from 4.8.17, 4.8.19
      have s4_8_20 : abs (x - c) = abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x + Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) := by parley_set_side
      -- 4.8.21. inequalities
      have s4_8_21 : Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) ≤ abs (Real.sqrt x - Real.sqrt c) * Real.sqrt x + Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) := by parley_order
      -- 4.8.22. transitivity, from 4.8.21, 4.8.20
      have s4_8_22 : Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) ≤ abs (x - c) := by parley_order
      -- 4.8.23. algebra, from 4.3
      have s4_8_23 : ε * Real.sqrt c = Real.sqrt c * ε := by linear_combination (norm := parley_norm) 0
      -- 4.8.24. transitivity, from 4.8.22, A2, 4.8.23
      have s4_8_24 : Real.sqrt c * abs (Real.sqrt x - Real.sqrt c) < Real.sqrt c * ε := by parley_order
      -- 4.8.25. mun:less-scaled x := |√x − √c|, y := ε, c := √c, from 4.3, 4.4, 4.8.7, 4.8.24
      have s4_8_25 : abs (Real.sqrt x - Real.sqrt c) < ε := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (Real.sqrt x - Real.sqrt c)) (y := ε) (c := Real.sqrt c) (by parley_set_side))).mpr s4_8_24
      -- 4.8.26. substitute g(x) = √x (line 4.8.8) into line 4.8.25
      have s4_8_26 : abs (g x - Real.sqrt c) < ε := by parley_subst_at s4_8_8 s4_8_25
      -- 4.8.27. substitute g(c) = √c (line 4.8.9) into line 4.8.26
      parley_subst_at s4_8_9 s4_8_26
    -- 4.9. exhibit, from 4.6, 4.7, 4.8
    exact ⟨ε * Real.sqrt c, ⟨s4_7, s4_8⟩⟩
  -- 5. def:continuous-on f := g, from 1, 4
  have r222_1 : Set.MapsTo g D (Set.univ : Set ℝ) := by parley_set_side
  exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := g) (D := D) s1)).mpr s4

end Parley.Tests.Elaborator.AMapOverASetBindingItsLetter.AMapOverASetBindingItsLetter
