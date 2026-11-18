module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/pairs.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Pairs.AFunctionOnPairs

theorem a_function_on_pairs (f : ℝ × ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)) (Set.univ : Set ℝ)) (hH2 : ∀ x : ℝ, ∀ y : ℝ, f (x, y) = x + y) :
    f ((1 : ℝ), (2 : ℝ)) = 3 := by
  -- 1. instantiate x := 1, y := 2 in H2
  have s1 : f ((1 : ℝ), (2 : ℝ)) = 1 + 2 := by exact (hH2 (1 : ℝ) (2 : ℝ))
  -- 2. calculation
  calc f ((1 : ℝ), (2 : ℝ)) = 1 + 2 := s1
    _ = 3 := by norm_num

end Parley.Tests.Notations.Pairs.AFunctionOnPairs
