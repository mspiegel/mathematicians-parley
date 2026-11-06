module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingAnItem

theorem a_chain_line_citing_an_item (n : ℤ) (hH1 : 0 ≤ n) (b : ℤ → ℝ) :
    (LeanBridges.Counting.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial n : ℝ) + b n - b n := by
  -- 1. calculation
  have s1 : (LeanBridges.Counting.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial n : ℝ) + b n - b n := by
    calc (LeanBridges.Counting.factorial (n + 1) : ℝ) = (LeanBridges.Counting.factorial n : ℝ) * ((n : ℝ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n) (by parley_side)); parley_side)
      _ = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial n : ℝ) + b n - b n := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingAnItem
