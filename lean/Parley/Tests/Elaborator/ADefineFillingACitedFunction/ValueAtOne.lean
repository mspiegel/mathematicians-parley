module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-define-filling-a-cited-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne

theorem value_at_one (f : ℤ → ℝ) (hH2 : ∀ k : ℤ, 0 < k → f k = (k : ℝ) + 1) :
    f 1 = 1 + 1 := by
  -- 1. instantiate k := 1 in H2
  exact_mod_cast (hH2 (1 : ℤ) (by norm_num))

end Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne
