module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/an-iff-of-this-corpus.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated

theorem zero_divides_restated (n : ℤ) :
    ((0 : ℤ) ∣ n ↔ n = 0) := by
  -- 1. mun:zero-divides
  exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))

end Parley.Tests.Elaborator.AnIffOfThisCorpus.ZeroDividesRestated
