module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/cube-congruent-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

theorem residue_mod_three (r : ℤ) (hH1 : 0 ≤ r) (hH2 : r < 3) :
    ((r = 0 ∨ r = 1) ∨ r = 2) := by
  -- 1. mun:range-from-bounds, from H2
  have s1 : r ∈ Finset.Icc (0 : ℤ) (3 - 1 : ℤ) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by parley_side) (x := r) (by parley_side) hH2) | exact ((Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by parley_side) (x := r) (by parley_side) hH2)).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by parley_side) (x := r) (by parley_side) hH2) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by parley_side) (x := r) (by parley_side) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by parley_side) (x := r) (by parley_side) hH2); parley_side)
  -- 2. inspection, from 1
  have s2 : (r = 0 ∨ r = 1) ∨ r = 2 := by parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree
