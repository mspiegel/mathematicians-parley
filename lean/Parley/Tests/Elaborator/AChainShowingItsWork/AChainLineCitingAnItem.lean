module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingAnItem

theorem a_chain_line_citing_an_item (n : ℤ) (hH1 : 0 ≤ n) (b : ℤ → ℝ) :
    (LeanBridges.Counting.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial n : ℝ) + b n - b n := by
  -- 1. calculation
  calc (LeanBridges.Counting.factorial (n + 1) : ℝ) = (LeanBridges.Counting.factorial n : ℝ) * ((n : ℝ) + 1) := by
        have hI : (LeanBridges.Counting.factorial (n + 1) : ℝ) = (LeanBridges.Counting.factorial n : ℝ) * ((n : ℝ) + 1) := by parley_instance_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)))
        exact hI
    _ = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial n : ℝ) + b n - b n := by parley_ring

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingAnItem
