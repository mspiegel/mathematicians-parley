module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-line-adding-what-the-checker-added.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineAddingWhatTheCheckerAdded.ARequiresLineAddingWhatTheCheckerAdded

theorem a_requires_line_adding_what_the_checker_added (p : ℝ) (hH2 : p > 0) (hH3 : ∃ n : ℕ, 0 < n ∧ (n : ℝ) > 2 / p) :
    (∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ) ≤ 1 / (2 / p)) := by
  -- 1. mun:quotient-positive x := 2, y := p, from H2
  have r14_1 : (2 : ℤ) > 0 := by parley_arith
  have s1 : 2 / p > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 : ℝ)) (y := p) (by parley_side) (by parley_side)); parley_side)
  -- 2. obtain m from H3
  obtain ⟨m, s2a, s2b⟩ := hH3
  try lift m to ℕ using le_of_lt s2a
  -- 3. inequalities
  have r21_1 : p ≠ 0 := by parley_side
  have s3 : (m : ℝ) ≥ 2 / p := by parley_order
  -- 4. mun:reciprocal-order x := 2/p, y := m, from 3
  have r27_1 : 2 / p > 0 := by parley_side
  have r27_2 : (m : ℤ) > 0 := by parley_order
  have r27_3 : p ≠ 0 := by parley_side
  have s4 : 1 / (m : ℝ) ≤ 1 / (2 / p) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) (by parley_side) (y := (m : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) (by parley_side) (y := (m : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) (by parley_side) (y := (m : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := 2 / p) (by parley_side) (y := (m : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
  -- 5. exhibit, from 4
  have s5 : ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ) ≤ 1 / (2 / p) := ⟨m, by parley_side, by parley_side⟩
  all_goals exact s5

end Parley.Tests.Elaborator.ARequiresLineAddingWhatTheCheckerAdded.ARequiresLineAddingWhatTheCheckerAdded
