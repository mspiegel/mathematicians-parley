module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.HalfTurn

theorem half_turn (x : ℝ) (hH2 : x ∈ ({-Real.pi, Real.pi} : Set ℝ)) :
    (∃ j : ℤ, x = (2 * (j : ℝ) + 1) * Real.pi) := by
  -- 1. def:pair u := −π, w := π, from H2
  have s1 : x = -Real.pi ∨ x = Real.pi := by first | exact ((Parley.Items.Stdlib.Sets.def_pair (x := x) (u := -Real.pi) (w := Real.pi))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_pair (x := x) (u := -Real.pi) (w := Real.pi))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_pair (x := x) (u := -Real.pi) (w := Real.pi))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_pair (x := x) (u := -Real.pi) (w := Real.pi))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_pair (x := x) (u := -Real.pi) (w := Real.pi))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_pair (x := x) (u := -Real.pi) (w := Real.pi))).mp (by parley_side); parley_side)
  -- 2. cases, from 1
  have s2 : ∃ j : ℤ, x = (2 * (j : ℝ) + 1) * Real.pi := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. algebra, from C1
      have s2_1 : x = (2 * -1 + 1) * Real.pi := by linear_combination (norm := parley_norm) hC1
      -- 2.2. exhibit, from 2.1
      have s2_2 : ∃ j : ℤ, x = (2 * (j : ℝ) + 1) * Real.pi := ⟨(-1 : ℤ), by parley_side⟩
      all_goals parley_side
    · skip
      -- 2.3. algebra, from C2
      have s2_3 : x = (2 * 0 + 1) * Real.pi := by linear_combination (norm := parley_norm) hC2
      -- 2.4. exhibit, from 2.3
      have s2_4 : ∃ j : ℤ, x = (2 * (j : ℝ) + 1) * Real.pi := ⟨(0 : ℤ), by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Stdlib.Geometry.HalfTurn
