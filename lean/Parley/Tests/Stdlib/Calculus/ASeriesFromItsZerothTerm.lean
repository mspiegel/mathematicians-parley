module

public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ASeriesFromItsZerothTerm

theorem a_series_from_its_zeroth_term (s : ℤ → ℝ) (hH2 : Filter.Tendsto (fun m : ℤ => (∑ j ∈ Finset.Icc (0 : ℤ) m, (s j : ℝ) : ℝ)) Filter.atTop (nhds 3)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ j ∈ Finset.Icc (0 : ℤ) n, (s j : ℝ)) = 3 := by
  -- 1. def:series-sum-from-zero t := s, L := 3, from H2
  have s1 : Filter.limUnder Filter.atTop (fun n : ℤ => ∑ j ∈ Finset.Icc (0 : ℤ) n, (s j : ℝ)) = 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum_from_zero (t := s) (L := (3 : ℝ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.ASeriesFromItsZerothTerm
