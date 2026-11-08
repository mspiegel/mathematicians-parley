module

public import AlgebraTactics
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.OddSquareOverEight

theorem odd_square_over_eight (N : ℤ) :
    ((2 * (N : ℚ) + 1) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
  set M : ℤ := 2 * N + 1 with hD1
  -- 1. calculation
  have s1 : ((M : ℚ) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
    calc ((M : ℚ) ^ 2 - 1) / 8 = ((2 * (N : ℚ) + 1) ^ 2 - 1) / 8 := by
          have hD1_w : (M : ℚ) = 2 * (N : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hD1; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst hD1_w | parley_subst hD1
      _ = (N : ℚ) * ((N : ℚ) + 1) / 2 := by parley_ring
  rw [hD1] at s1; exact_mod_cast s1

end Parley.Proofs.Setmm.Parity.OddSquareOverEight
