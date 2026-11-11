module

public import InstanceTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ASquareIsNotOneToOne

theorem a_square_is_not_one_to_one (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = x ^ 2) :
    ¬ (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ)) := by
  -- 1. D1
  have s1 : f (-1) = (-1) ^ 2 := by simp (disch := omega) only [hD1]
  -- 2. D1
  have s2 : f 1 = 1 ^ 2 := by simp (disch := omega) only [hD1]
  -- 3. calculation
  have s3 : f (-1) = f 1 := by
    calc f (-1) = (-1) ^ 2 := by exact s1
      _ = 1 ^ 2 := by norm_num
      _ = f 1 := by exact s2.symm
  -- 4. contradiction
  intro hS
  -- 4.1. def:one-to-one, from S
  have s4_1 : ∀ s : ℝ, ∀ t : ℝ, f s = f t → s = t := by
    have hI : ∀ s : ℝ, ∀ t : ℝ, f s = f t → s = t := by parley_instance_cast ((((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp hS).2)
    exact hI
  -- 4.2. instantiate s := −1, t := 1 in line 4.1, from 3
  have s4_2 : (-1 : ℝ) = 1 := by exact (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side))
  exact absurd s4_2 (by norm_num)

end Parley.Tests.Notations.Functions.ASquareIsNotOneToOne
