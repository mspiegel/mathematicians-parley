module

public import AlgebraTactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalNegative

theorem rational_negative (A : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp ⟨_, rfl⟩
  -- 2. algebra, from 1
  have s2 : -A = -(p : ℚ) / (q : ℚ) := by linear_combination (norm := parley_field) (-1) * s1b
  -- 3. exhibit, from 2
  have s3 : ∃ a : ℤ, ∃ b : ℤ, 0 < b ∧ -A = (a : ℚ) / (b : ℚ) := ⟨-p, q, s1a, by (have h := s2; push_cast at h ⊢; all_goals exact h)⟩
  -- 4. def:rational x := −A, from 3
  exact trivial

end Parley.Proofs.Setmm.RationalClosure.RationalNegative
