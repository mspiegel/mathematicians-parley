module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalProduct

theorem rational_product (A : ℚ) (B : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  -- 2. obtain r, s: def:rational x := B
  obtain ⟨r, s, s2a, s2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp (by parley_side)
  -- 3. calculation
  have s3 : A * B = (p : ℚ) * (r : ℚ) / ((q : ℚ) * (s : ℚ)) := by
    calc A * B = (p : ℚ) / (q : ℚ) * B := by (have h := congrArg (fun t : ℚ => t * B) s1b; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (p : ℚ) / (q : ℚ) * ((r : ℚ) / (s : ℚ)) := by (have h := congrArg (fun t : ℚ => (p : ℚ) / (q : ℚ) * t) s2b; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (p : ℚ) * (r : ℚ) / ((q : ℚ) * (s : ℚ)) := by parley_ring
  -- 4. exhibit, from 3
  have s4 : ∃ a : ℤ, ∃ b : ℤ, 0 < b ∧ A * B = (a : ℚ) / (b : ℚ) := ⟨p * r, q * s, by parley_side, by (have h := s3; push_cast at h ⊢; all_goals exact h)⟩
  -- 5. def:rational x := A·B, from 4
  exact trivial

end Parley.Proofs.Setmm.RationalClosure.RationalProduct
