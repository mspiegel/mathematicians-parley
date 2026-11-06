module

public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/bound-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundNames.SeriesUnderItsOwnLetters

theorem series_under_its_own_letters (hH1 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ) : ℝ)) Filter.atTop (nhds 1)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ)) = 1 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. def:series-sum L := 1, from H1, 1
  have s2 : Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ)) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Tests.Elaborator.BoundNames.SeriesUnderItsOwnLetters
