module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PairsApartByAlgebra

theorem pairs_apart_by_algebra (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : a ≠ c) :
    ¬ ((a, b) : ℝ × ℝ) = (c, d) := by
  -- 1. algebra, from H5
  exact fun h => (show a ≠ c by intro h; exact hH5 (by linear_combination h)) (congrArg Prod.fst h)

end Parley.Tests.Elaborator.PairsCompared.PairsApartByAlgebra
