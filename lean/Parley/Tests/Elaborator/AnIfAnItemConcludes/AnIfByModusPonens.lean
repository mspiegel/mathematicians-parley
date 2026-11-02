module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from tests/elaborator/an-if-an-item-concludes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIfAnItemConcludes.AnIfByModusPonens

theorem an_if_by_modus_ponens (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = 0 → b = 0 → c = 0) (hH5 : a = 0) :
    (b = 0 → c = 0) := by
  -- 1. mun:modus-ponens, from H4, H5
  have s1 : b = 0 → c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0) (Q := b = 0 → c = 0) (by parley_side) (by parley_side))
  all_goals parley_side

end Parley.Tests.Elaborator.AnIfAnItemConcludes.AnIfByModusPonens
