module

public import AlgebraTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/compose-rational-and-line.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ComposeRationalAndLine.ComposeRationalAndLine

theorem compose_rational_and_line (f : ℝ → ℝ) (g : ℝ → ℝ) (hH3 : ∀ x : ℝ, f x = 1 / (x ^ 2 + 1)) (hH4 : ∀ x : ℝ, g x = 3 * x + 2) :
    (∀ x : ℝ, (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 ∧ (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1)) := by
  -- 1. proof
  intro x
  -- 1.1. mun:function-value
  -- 1.2. mun:square-nonneg
  have s1_2 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 1.3. inequalities, from 1.2
  have s1_3 : x ^ 2 + 1 > 0 := by parley_order
  -- 1.4. calculation
  have r27_1 : x ^ 2 + 1 ≠ 0 := by parley_set_side
  have s1_4 : (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 := by
    calc (g ∘ f) x = g (f x) := by exact (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := f) (g := g) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side))
      _ = 3 * f x + 2 := by exact (hH4 (f x))
      _ = 3 * (1 / (x ^ 2 + 1)) + 2 := by (have h := congrArg (fun t : ℝ => 3 * t + 2) (hH3 x); push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 3 / (x ^ 2 + 1) + 2 := by parley_ring
  -- 1.5. mun:function-value f := g
  -- 1.6. calculation
  have s1_6 : (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1) := by
    calc (f ∘ g) x = f (g x) := by exact (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := g) (g := f) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side))
      _ = 1 / (g x ^ 2 + 1) := by exact (hH3 (g x))
      _ = 1 / ((3 * x + 2) ^ 2 + 1) := by (have h := congrArg (fun t : ℝ => 1 / (t ^ 2 + 1)) (hH4 x); push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 1.7. join 1.4, 1.6
  have s1_7a : (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 := by parley_set_side
  have s1_7b : (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1) := by parley_set_side
  exact ⟨s1_7a, s1_7b⟩

end Parley.Proofs.Hammack.ComposeRationalAndLine.ComposeRationalAndLine
