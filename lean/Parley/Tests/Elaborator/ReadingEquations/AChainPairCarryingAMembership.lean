module

public import Mathlib.Analysis.Complex.Order
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairCarryingAMembership

theorem a_chain_pair_carrying_a_membership (x : ℂ) (y : ℂ) (r : ℝ) (hH4 : x = y ∧ y = (r : ℂ)) :
    (∃ m : ℝ, (m : ℂ) = x) := by
  -- 1. membership, from H4
  exact (⟨r, by exact_mod_cast (hH4.2).symm⟩ : ∃ m : ℝ, (m : ℂ) = y).imp (fun _ h => h.trans (hH4.1).symm)

end Parley.Tests.Elaborator.ReadingEquations.AChainPairCarryingAMembership
