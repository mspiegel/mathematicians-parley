module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-define-filling-a-cited-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne

theorem value_at_one (f : ℤ → ℝ) (hH2 : ∀ k : ℤ, 0 < k → f k = (k : ℝ) + 1) :
    f 1 = 1 + 1 := by
  -- 1. instantiate k := 1 in H2
  exact_mod_cast (hH2 (1 : ℤ) (by parley_side))

end Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne
