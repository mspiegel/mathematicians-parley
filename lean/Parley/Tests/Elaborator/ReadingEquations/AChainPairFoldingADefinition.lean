module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairFoldingADefinition

theorem a_chain_pair_folding_a_definition (n : ℤ) (hH1 : 0 < n) (m : ℤ) (hH2 : 0 < m) (hH3 : (ArithmeticFunction.sigma 1 n.toNat : ℤ) = m ∧ m = 2 * n) :
    ArithmeticFunction.sigma 1 n.toNat = 2 * n.toNat := by
  -- 1. def:perfect, from H3
  exact ((Parley.Items.Stdlib.Divisibility.def_perfect (n := n) hH1)).mpr (Eq.trans (hH3.1) hH3.2)

end Parley.Tests.Elaborator.ReadingEquations.AChainPairFoldingADefinition
