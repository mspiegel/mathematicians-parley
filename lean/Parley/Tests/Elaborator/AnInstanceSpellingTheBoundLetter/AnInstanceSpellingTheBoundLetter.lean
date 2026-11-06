module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/an-instance-spelling-the-bound-letter.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceSpellingTheBoundLetter.AnInstanceSpellingTheBoundLetter

theorem an_instance_spelling_the_bound_letter (x : ℤ → ℝ) (A : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds A)) :
    (∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - A) < ε / 2))) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - A) < ε / 2)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 2 > 0 := by parley_order
    -- 1.2. def:tends-to L := A, from H3
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - A) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := A))).mp (by parley_side); parley_side)
    -- 1.3. instantiate ε := ε/2 in line 1.2, from 1.1
    have s1_3 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - A) < ε / 2) := by first | exact (s1_2 (ε / 2) (by parley_side)) | exact ((s1_2 (ε / 2) (by parley_side))).symm | simpa using (s1_2 (ε / 2) (by parley_side)) | exact_mod_cast (s1_2 (ε / 2) (by parley_side)) | (have h := (s1_2 (ε / 2) (by parley_side)); parley_side)
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AnInstanceSpellingTheBoundLetter.AnInstanceSpellingTheBoundLetter
