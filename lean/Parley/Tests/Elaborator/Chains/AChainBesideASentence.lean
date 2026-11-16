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

namespace Parley.Tests.Elaborator.Chains.AChainBesideASentence

theorem a_chain_beside_a_sentence (x : ℝ) (y : ℝ) (z : ℝ) (hH4a : x = y ∧ y = z) (hH4b : x + 1 = 5) :
    z + 1 = 5 := by
  -- 1. substitute x = z (H4) into H4
  exact Eq.subst (motive := (fun t : ℝ => t + 1 = 5)) (Eq.trans (hH4a.1) hH4a.2) hH4b

end Parley.Tests.Elaborator.Chains.AChainBesideASentence
