module

public import InstanceTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ADefinitionUnfoldingTheSecondSentence

theorem a_definition_unfolding_the_second_sentence (t : ℤ) (hH1 : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) ∩ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) :
    (∃ n : ℤ, t = 3 * n) := by
  -- 1. def:intersection u := t, from H1
  have s1a : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp hH1).1
  have s1b : t ∈ (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ)) (Z := (fun n : ℤ => 3 * n) '' (Set.univ : Set ℤ)) (u := t))).mp hH1).2
  -- 2. def:set-image u := t, from 1
  have hI : ∃ s : ℤ, t = 3 * s := by parley_instance (((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 3 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp s1b)
  exact hI

end Parley.Tests.Elaborator.TextbookExerciseShapes.ADefinitionUnfoldingTheSecondSentence
