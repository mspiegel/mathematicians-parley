module

public import Batteries.Tactic.Init
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairContradicted

theorem a_chain_pair_contradicted (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = b ∧ b = c) :
    a = c := by
  -- 1. contradiction
  by_contra (hS : a ≠ c)
  -- 1.1. restate S
  have s1_1 : a ≠ c := by exact hS
  exact s1_1 (Eq.trans (hH4.1) hH4.2)

end Parley.Tests.Elaborator.ReadingEquations.AChainPairContradicted
