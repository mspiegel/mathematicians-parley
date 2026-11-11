module

public import Tactics
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedFoldingADefinition

theorem an_equation_turned_folding_a_definition (n : ℤ) (hH1 : 0 < n) (hH2 : 2 * n = (ArithmeticFunction.sigma 1 n.toNat : ℤ)) :
    ArithmeticFunction.sigma 1 n.toNat = 2 * n.toNat := by
  -- 1. def:perfect, from H2
  exact ((Parley.Items.Stdlib.Divisibility.def_perfect (n := n) hH1)).mpr hH2.symm

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedFoldingADefinition
