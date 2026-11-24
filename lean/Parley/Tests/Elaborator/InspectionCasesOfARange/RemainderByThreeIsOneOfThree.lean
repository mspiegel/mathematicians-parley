module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.RemainderByThreeIsOneOfThree

theorem remainder_by_three_is_one_of_three (n : ℤ) :
    n % (3 : ℤ) ≤ 2 := by
  -- 1. mun:mod-less b := 3
  have s1 : n % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by norm_num))
  -- 2. mun:range-from-bounds, from 1
  have s2 : n % (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (3 - 1 : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := (3 : ℤ)) (by norm_num) (x := n % (3 : ℤ)) (Int.emod_nonneg _ (ne_of_gt (by norm_num))) s1)
  -- 3. inspection, from 2
  have s3 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by (have h := s2; norm_num [Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)
  -- 4. cases, from 3
  rcases s3 with (hC1 | hC2) | hC3
  · skip
    -- 4.1. calculation
    calc n % (3 : ℤ) = 0 := hC1
      _ ≤ 2 := by norm_num
  · skip
    -- 4.2. calculation
    calc n % (3 : ℤ) = 1 := hC2
      _ ≤ 2 := by norm_num
  · skip
    -- 4.3. calculation
    calc n % (3 : ℤ) = 2 := hC3
      _ ≤ 2 := by norm_num

end Parley.Tests.Elaborator.InspectionCasesOfARange.RemainderByThreeIsOneOfThree
