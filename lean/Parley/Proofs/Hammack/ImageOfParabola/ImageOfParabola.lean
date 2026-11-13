module

public import ArithTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-parabola.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfParabola.ImageOfParabola

theorem image_of_parabola (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x ^ 2 + 3) :
    f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) = (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by
  -- 1. mun:interval-real a := −3, b := 5
  have s1 : (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ)))
  -- 2. proof
  have s2 : ∀ y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)), y ∈ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by
    intro y hK1
    -- 2.1. obtain s: def:image u := y, Y := [−3, 5], from K1, 1
    obtain ⟨s, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (u := y) (W := Set.univ) s1 (Set.mapsTo_univ _ _))).mp hK1
    -- 2.2. def:interval a := −3, b := 5, x := s, from 2.1
    have s2_2a : -3 ≤ s := by exact (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp s2_1a).1.2
    have s2_2b : s ≤ 5 := by exact (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp s2_1a).2
    -- 2.3. calculation
    have s2_3 : y = s ^ 2 + 3 := by
      calc y = f s := s2_1b
        _ = s ^ 2 + 3 := by exact (hH2 s)
    -- 2.4. mun:square-nonneg x := s
    have s2_4 : s ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := s))
    -- 2.5. inequalities
    have s2_5 : s ^ 2 + 3 ≥ 3 := by linarith only [s2_4]
    -- 2.6. calculation
    have s2_6 : y ≥ 3 := by
      calc y = s ^ 2 + 3 := s2_3
        _ ≥ 3 := s2_5
    -- 2.7. inequalities
    have s2_7 : s + 3 ≥ 0 := by linarith only [s2_2a]
    -- 2.8. inequalities
    have s2_8 : 5 - s ≥ 0 := by linarith only [s2_2b]
    -- 2.9. mun:product-nonneg x := s + 3, y := 5 − s, from 2.7, 2.8
    have s2_9 : (s + 3) * (5 - s) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := s + 3) (y := 5 - s) s2_7 s2_8)
    -- 2.10. inequalities
    have s2_10 : s ^ 2 + 3 ≤ 2 * s + 18 := by linarith only [s2_9]
    -- 2.11. inequalities
    have s2_11 : 2 * s + 18 ≤ 28 := by linarith only [s2_2b]
    -- 2.12. calculation
    have s2_12 : y ≤ 28 := by
      calc y = s ^ 2 + 3 := s2_3
        _ ≤ 2 * s + 18 := s2_10
        _ ≤ 28 := s2_11
    -- 2.13. membership, from 2.3
    -- 2.14. def:interval a := 3, b := 28, x := y, from 2.6, 2.12, 2.13
    exact ((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mpr ⟨⟨by trivial, s2_6⟩, s2_12⟩
  -- 3. def:subset, from 2
  have s3 : f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) ⊆ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)))).mpr s2
  -- 4. proof
  have s4 : ∀ y ∈ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ), y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by
    intro y hK2
    -- 4.1. def:interval a := 3, b := 28, x := y, from K2
    have s4_1a : 3 ≤ y := by exact (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp hK2).1.2
    have s4_1b : y ≤ 28 := by exact (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp hK2).2
    -- 4.2. inequalities
    have s4_2 : y - 3 ≥ 0 := by linarith only [s4_1a]
    -- 4.3. def:sqrt x := y − 3, from 4.2
    have s4_3a : Real.sqrt (y - 3) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := y - 3) s4_2)
    have s4_3b : Real.sqrt (y - 3) ^ 2 = y - 3 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) s4_2)
    -- 4.4. inequalities
    have s4_4 : y - 3 ≤ 25 := by linarith only [s4_1b]
    -- 4.5. calculation
    have s4_5 : Real.sqrt (y - 3) ^ 2 ≤ 5 ^ 2 := by
      calc Real.sqrt (y - 3) ^ 2 = y - 3 := s4_3b
        _ ≤ 25 := s4_4
        _ = 5 ^ 2 := by norm_num
    -- 4.6. mun:square-le x := √(y − 3), y := 5, from 4.3, 4.5
    have r121_1 : (0 : ℤ) ≤ 5 := by parley_arith
    have s4_6 : Real.sqrt (y - 3) ≤ 5 := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (y - 3)) (y := (5 : ℝ)) s4_3a (by norm_num))).mpr s4_5
    -- 4.7. inequalities, from 4.3
    have s4_7 : -3 ≤ Real.sqrt (y - 3) := by linarith only [s4_3a]
    -- 4.8. def:interval a := −3, b := 5, x := √(y − 3), from 4.3, 4.6, 4.7
    have s4_8 : Real.sqrt (y - 3) ∈ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := Real.sqrt (y - 3)) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mpr ⟨⟨by trivial, s4_7⟩, s4_6⟩
    -- 4.9. instantiate x := √(y − 3) in H2, from 4.3
    have s4_9 : f (Real.sqrt (y - 3)) = Real.sqrt (y - 3) ^ 2 + 3 := by exact (hH2 (Real.sqrt (y - 3)))
    -- 4.10. mun:value-in-image Y := [−3, 5], s := √(y − 3), from 1, 4.8
    have s4_10 : f (Real.sqrt (y - 3)) ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) s1 s4_8 (Set.mapsTo_univ _ _))
    -- 4.11. substitute
    have c1 : f (Real.sqrt (y - 3)) = y := by linear_combination (norm := parley_norm) s4_3b + s4_9
    have row1 : y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by (have h := Eq.subst (motive := (fun t : ℝ => t ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)))) c1 s4_10; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 5. def:subset, from 4
  have s5 : (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) ⊆ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := ((Parley.Items.Stdlib.Sets.def_subset (X := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) (Y := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))))).mpr s4
  -- 6. mun:subset-antisymmetric, from 3, 5
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5)

end Parley.Proofs.Hammack.ImageOfParabola.ImageOfParabola
