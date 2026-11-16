module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Chains.ChainCitedForAPair

theorem chain_cited_for_a_pair (x : ℝ) (y : ℝ) (z : ℝ) (w : ℝ) (hH5 : x = y ∧ y = z ∧ z = w) (hH6 : x + 1 = 5) (hH7 : w * 2 = 6) :
    w + 1 = 5 ∧ x * 2 = 6 := by
  -- 1. substitute x = w (H5) into H6
  have s1 : w + 1 = 5 := Eq.subst (motive := (fun t : ℝ => t + 1 = 5)) (Eq.trans (Eq.trans (hH5.1) hH5.2.1) hH5.2.2) hH6
  -- 2. substitute w = x (H5) into H7
  have s2 : x * 2 = 6 := Eq.subst (motive := (fun t : ℝ => t * 2 = 6)) (Eq.trans (Eq.trans (hH5.1) hH5.2.1) hH5.2.2).symm hH7
  -- 3. join 1, 2
  have s3a : w + 1 = 5 := s1
  have s3b : x * 2 = 6 := s2
  exact ⟨s3a, s3b⟩

end Parley.Tests.Elaborator.Chains.ChainCitedForAPair
