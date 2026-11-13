module

public import ArithTactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.AbsMinusThree

theorem abs_minus_three :
    (abs (-3) : ℤ) = 3 := by
  -- 1. arithmetic
  have s1 : (-3 : ℤ) < 0 := by parley_arith
  -- 2. def:abs x := −3, from 1
  have s2 : (abs (-3) : ℤ) = -(-3) := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by norm_num)
  -- 3. calculation
  calc (abs (-3) : ℤ) = -(-3) := s2
    _ = 3 := by norm_num

end Parley.Tests.Notations.Numbers.AbsMinusThree
