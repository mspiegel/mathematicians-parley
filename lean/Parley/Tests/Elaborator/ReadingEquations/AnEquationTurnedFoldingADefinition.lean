module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedFoldingADefinition

theorem an_equation_turned_folding_a_definition (n : ℤ) (hH1 : 0 < n) (hH2 : 2 * n = (ArithmeticFunction.sigma 1 n.toNat : ℤ)) :
    ArithmeticFunction.sigma 1 n.toNat = 2 * n.toNat := by
  -- 1. def:perfect, from H2
  have s1 : ArithmeticFunction.sigma 1 n.toNat = 2 * n.toNat := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_perfect (n := n) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_perfect (n := n) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedFoldingADefinition
