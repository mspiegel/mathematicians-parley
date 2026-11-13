module

public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-cited-line-narrows-a-letter.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedLineNarrowsALetter.ACitedLineNarrowsALetter

theorem a_cited_line_narrows_a_letter (q : ℤ) (hH2 : q ≥ 0) (hH3 : ∀ k : ℤ, 0 ≤ k → k + 1 > 0) :
    3 * q + 1 + 1 > 0 := by
  -- 1. mun:nat0-as-int n := q, from H2
  have s1 : 0 ≤ q := by
    have hI : 0 ≤ q := by parley_instance (((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := q))).mpr ⟨⟨_, rfl⟩, hH2⟩)
    exact hI
  -- 2. instantiate k := 3q + 1 in H3, from 1
  exact (hH3 (3 * q + 1) (add_nonneg (mul_nonneg (by norm_num) (s1)) (by norm_num)))

end Parley.Tests.Elaborator.ACitedLineNarrowsALetter.ACitedLineNarrowsALetter
