module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/an-if-an-item-concludes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIfAnItemConcludes.AnIfByABiconditional

theorem an_if_by_a_biconditional (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = 0 ↔ b = 0 → c = 0) (hH5 : a = 0) :
    (b = 0 → c = 0) := by
  -- 1. mun:iff-from-left, from H4, H5
  have s1 : b = 0 → c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := a = 0) (Q := b = 0 → c = 0) hH4 hH5) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := a = 0) (Q := b = 0 → c = 0) hH4 hH5)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := a = 0) (Q := b = 0 → c = 0) hH4 hH5) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := a = 0) (Q := b = 0 → c = 0) hH4 hH5) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := a = 0) (Q := b = 0 → c = 0) hH4 hH5); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AnIfAnItemConcludes.AnIfByABiconditional
