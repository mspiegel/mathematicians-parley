module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineInstantiating

theorem a_chain_line_instantiating (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x + 1) :
    f 2 = 3 := by
  -- 1. calculation
  calc f 2 = 2 + 1 := by exact (hH2 (2 : ℝ))
    _ = 3 := by norm_num

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineInstantiating
