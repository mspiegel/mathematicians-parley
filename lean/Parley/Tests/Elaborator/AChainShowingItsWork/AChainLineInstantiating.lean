module

public import LeanBridges

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineInstantiating

theorem a_chain_line_instantiating (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x + 1) :
    f 2 = 3 := by
  -- 1. calculation
  have s1 : f 2 = 3 := by
    calc f 2 = 2 + 1 := by first | linear_combination (norm := parley_norm) (hH2 (2 : ℝ)) | (have h := (hH2 (2 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (2 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (2 : ℝ)) | exact_mod_cast ((hH2 (2 : ℝ))).symm | (have h := (hH2 (2 : ℝ)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (2 : ℝ)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (2 : ℝ)); parley_int_power h) | (have h := (hH2 (2 : ℝ)); parley_side)
      _ = 3 := by norm_num
  all_goals parley_side

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineInstantiating
