module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ALimitUnfoldedOnTheLine

theorem a_limit_unfolded_on_the_line (f : ℝ → ℝ) (c : ℝ) (L : ℝ) (hH4 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L)) :
    (∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) := by
  -- 1. def:limit-at D := ℝ, from H4
  have r93_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ALimitUnfoldedOnTheLine
