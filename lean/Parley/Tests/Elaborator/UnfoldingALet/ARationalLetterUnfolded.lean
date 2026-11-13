module

public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/unfolding-a-let.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.UnfoldingALet.ARationalLetterUnfolded

theorem a_rational_letter_unfolded (A : ℚ) :
    (∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ A = (p : ℚ) / (q : ℚ)) := by
  -- 1. def:rational x := A
  exact ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp ⟨_, rfl⟩

end Parley.Tests.Elaborator.UnfoldingALet.ARationalLetterUnfolded
