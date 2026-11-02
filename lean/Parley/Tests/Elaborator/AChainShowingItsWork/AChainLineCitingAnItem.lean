module

public import LeanBridges
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingAnItem

theorem a_chain_line_citing_an_item (n : ℕ) (b : ℤ → ℝ) :
    (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℝ) = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ) + b (n : ℤ) - b (n : ℤ) := by
  -- 1. calculation
  have s1 : (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℝ) = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ) + b (n : ℤ) - b (n : ℤ) := by
    calc (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℝ) = (LeanBridges.Counting.factorial (n : ℤ) : ℝ) * ((n : ℝ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := n))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); qify; linear_combination (norm := parley_norm) h)
      _ = ((n : ℝ) + 1) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ) + b (n : ℤ) - b (n : ℤ) := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingAnItem
