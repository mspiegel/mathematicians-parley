module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalProduct

theorem rational_product (A : ℚ) (B : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp ⟨_, rfl⟩
  -- 2. obtain r, s: def:rational x := B
  obtain ⟨r, s, s2a, s2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp ⟨_, rfl⟩
  -- 3. calculation
  have s3 : A * B = (p : ℚ) * (r : ℚ) / ((q : ℚ) * (s : ℚ)) := by
    calc A * B = (p : ℚ) / (q : ℚ) * B := congrArg (fun t : ℚ => t * B) s1b
      _ = (p : ℚ) / (q : ℚ) * ((r : ℚ) / (s : ℚ)) := congrArg (fun t : ℚ => (p : ℚ) / (q : ℚ) * t) s2b
      _ = (p : ℚ) * (r : ℚ) / ((q : ℚ) * (s : ℚ)) := by have hz1 : (q : ℚ) ≠ 0 := (by positivity); have hz2 : (s : ℚ) ≠ 0 := (by positivity); field
  -- 4. exhibit, from 3
  have s4 : ∃ a : ℤ, ∃ b : ℤ, 0 < b ∧ A * B = (a : ℚ) / (b : ℚ) := ⟨p * r, q * s, mul_pos (s1a) (s2a), by (have h := s3; push_cast at h ⊢; exact h)⟩
  -- 5. def:rational x := A·B, from 4
  exact trivial

end Parley.Proofs.Setmm.RationalClosure.RationalProduct
