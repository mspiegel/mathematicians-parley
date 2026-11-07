module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-cited-line-narrows-a-letter.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLineNarrowsALetter.ACitedLineNarrowsALetter

theorem a_cited_line_narrows_a_letter (q : ℤ) (hH2 : q ≥ 0) (hH3 : ∀ k : ℤ, 0 ≤ k → k + 1 > 0) :
    3 * q + 1 + 1 > 0 := by
  -- 1. mun:nat0-as-int n := q, from H2
  have s1 : 0 ≤ q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := q))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := q))).mpr (by parley_side); parley_side)
  -- 2. instantiate k := 3q + 1 in H3, from 1
  have s2 : 3 * q + 1 + 1 > 0 := by first | linarith [(hH3 (3 * q + 1) (by parley_side))] | (have h := (hH3 (3 * q + 1) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH3 (3 * q + 1) (by parley_side)) | (have h := (hH3 (3 * q + 1) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Tests.Elaborator.ACitedLineNarrowsALetter.ACitedLineNarrowsALetter
