module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/bound-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundNames.SeriesUnderItsOwnLetters

theorem series_under_its_own_letters (hH1 : Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ) : ℝ)) Filter.atTop (nhds 1)) :
    Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ)) = 1 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. def:series-sum L := 1, from H1, 1
  have s2 : Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ)) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Tests.Elaborator.BoundNames.SeriesUnderItsOwnLetters
