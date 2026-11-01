module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingATheorem

theorem a_chain_line_citing_a_theorem (a : ℝ) (b : ℝ) (hH3 : a * 2 = b * 2) :
    a = b + 0 := by
  -- 1. calculation
  have r60_1 : (2 : ℤ) ≠ 0 := by parley_arith
  have s1 : a = b + 0 := by
    calc a = b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a) (b := b) (c := (2 : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a) (b := b) (c := (2 : ℝ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a) (b := b) (c := (2 : ℝ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a) (b := b) (c := (2 : ℝ)) (by parley_side) (by parley_side))).symm
      _ = b + 0 := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingATheorem
