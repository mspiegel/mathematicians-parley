module

public import AlgebraTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartByMembership

theorem an_and_part_by_membership (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ (∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ))) :
    (∃ m : ℝ, (m : ℂ) = (b : ℂ) ^ (1 / 2 : ℂ) + 1) := by
  -- 1. membership, from H3
  (exact ⟨(Classical.choose hH3.2 : ℝ) + 1, by push_cast; (try simp only [Classical.choose_spec hH3.2]); all_goals parley_ring⟩)

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartByMembership
