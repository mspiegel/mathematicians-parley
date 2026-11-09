module

public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ALogarithmOfASquare

theorem a_logarithm_of_a_square (s : ℝ) (hH2 : s > 0) :
    Real.log (s ^ 2) = 2 * Real.log s := by
  -- 1. mun:ln-power x := s, n := 2, from H2
  have hI : Real.log (s ^ 2) = 2 * Real.log s := by parley_instance ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) hH2))
  exact hI

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ALogarithmOfASquare
