module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Tests.Elaborator.APhraseDefined

/-! Written from tests/elaborator/a-phrase-imported.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseImported.TenIsTriangular

theorem ten_is_triangular :
    ((0 : ℤ) < 10 ∧ (∃ k : ℤ, 0 < k ∧ 10 = (k : ℚ) * ((k : ℚ) + 1) / 2)) := by
  -- 1. arithmetic
  have s1 : (10 : ℚ) = 4 * (4 + 1) / 2 := by norm_num
  -- 2. exhibit, from 1
  have s2 : ∃ k : ℤ, 0 < k ∧ 10 = (k : ℚ) * ((k : ℚ) + 1) / 2 := ⟨(4 : ℤ), by norm_num, by norm_num⟩
  -- 3. def:triangular-number n := 10, from 2
  exact ⟨by norm_num, s2⟩

end Parley.Tests.Elaborator.APhraseImported.TenIsTriangular
