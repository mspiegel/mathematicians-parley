module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.Range0

theorem range0 (n : ℤ) (hH1 : 0 ≤ n) (k : ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (0 : ℤ) n) :
    (0 ≤ k ∧ k ≤ n) := by
  -- 1. def:sums-range0, from H3
  have s1 : 0 ≤ k ∧ k ≤ n := by first | exact ((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) (by parley_side))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.Range0
