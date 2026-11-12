module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.RemainderByThreeIsOneOfThree

theorem remainder_by_three_is_one_of_three (n : ℤ) :
    n % (3 : ℤ) ≤ 2 := by
  -- 1. mun:mod-natural b := 3
  have s1 : 0 ≤ n % (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by norm_num))
  -- 2. mun:mod-less b := 3
  have s2 : n % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by norm_num))
  -- 3. mun:range-from-bounds, from 1, 2
  have s3 : n % (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (3 - 1 : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by norm_num) (x := n % (3 : ℤ)) s1 s2)
  -- 4. inspection, from 3
  have s4 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by parley_side
  -- 5. cases, from 4
  rcases s4 with (hC1 | hC2) | hC3
  · skip
    -- 5.1. calculation
    calc n % (3 : ℤ) = 0 := by parley_side
      _ ≤ 2 := by norm_num
  · skip
    -- 5.2. calculation
    calc n % (3 : ℤ) = 1 := by parley_side
      _ ≤ 2 := by norm_num
  · skip
    -- 5.3. calculation
    calc n % (3 : ℤ) = 2 := by parley_side
      _ ≤ 2 := by norm_num

end Parley.Tests.Elaborator.InspectionCasesOfARange.RemainderByThreeIsOneOfThree
