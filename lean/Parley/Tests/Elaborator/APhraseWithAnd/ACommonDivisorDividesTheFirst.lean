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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Tests.Elaborator.APhraseWithAnd

/-! Written from tests/elaborator/a-phrase-with-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseWithAnd.ACommonDivisorDividesTheFirst

theorem a_common_divisor_divides_the_first (a : ℤ) (b : ℤ) (d : ℤ) (hH4 : ((True ∧ d ∣ a) ∧ d ∣ b) ∧ d > 0) :
    d ∣ a := by
  -- 1. restate H4
  have s1 : (True ∧ d ∣ a) ∧ d ∣ b := by exact hH4.1
  -- 2. D1, from 1
  have s2 : (True ∧ d ∣ a) ∧ d ∣ b := s1
  -- 3. restate 2
  exact s2.1.2

end Parley.Tests.Elaborator.APhraseWithAnd.ACommonDivisorDividesTheFirst
