module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWaySubstitutedInto

theorem a_congruence_the_other_way_substituted_into (a : ℤ) (b : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : b ≡ a [ZMOD n]) (hH6 : a = c) :
    c ≡ b [ZMOD n] := by
  -- 1. substitute a = c (H6) into H5
  parley_subst_at hH6 hH5

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWaySubstitutedInto
