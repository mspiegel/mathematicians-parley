module

public import InstanceTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ASquareIsNotOnto

theorem a_square_is_not_onto (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = x ^ 2) :
    ¬ (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.SurjOn f (Set.univ : Set ℝ) (Set.univ : Set ℝ)) := by
  -- 1. contradiction
  intro hS
  -- 1.1. def:onto, from S
  have s1_1 : ∀ y : ℝ, ∃ x : ℝ, y = f x := by
    have hI : ∀ y : ℝ, ∃ x : ℝ, y = f x := by parley_instance_cast ((((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (Set.mapsTo_univ _ _))).mp hS).2)
    exact hI
  -- 1.2. instantiate y := −1 in line 1.1
  have s1_2 : ∃ x : ℝ, -1 = f x := by exact (s1_1 (-1 : ℝ))
  -- 1.3. obtain x from line 1.2
  obtain ⟨x, s1_3⟩ := s1_2
  -- 1.4. D1
  have s1_4 : f x = x ^ 2 := by simp (disch := omega) only [hD1]
  -- 1.5. mun:square-nonneg
  have s1_5 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 1.6. calculation
  have s1_6 : -1 = x ^ 2 := by
    calc (-1 : ℝ) = f x := s1_3
      _ = x ^ 2 := s1_4
  -- 1.7. substitute −1 = x² (line 1.6) into line 1.5
  have s1_7 : (-1 : ℝ) ≥ 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t ≥ 0)) s1_6.symm s1_5; push_cast at h ⊢; all_goals exact_mod_cast h)
  exact absurd s1_7 (by norm_num)

end Parley.Tests.Notations.Functions.ASquareIsNotOnto
