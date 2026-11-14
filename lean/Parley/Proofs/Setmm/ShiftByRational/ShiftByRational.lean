module

public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
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
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/shift-by-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ShiftByRational.ShiftByRational

theorem shift_by_rational (A : ℂ) (B : ℚ) :
    (True ∧ (∃ m : ℚ, (m : ℂ) = A + (B : ℂ)) ↔ (∃ m : ℚ, (m : ℂ) = A)) := by
  -- 1. obtain r, s: def:rational x := B
  obtain ⟨r, s, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp ⟨_, rfl⟩
  -- 2. both directions
  constructor
  · skip
    intro hD1
    -- 2.1. obtain p, q: def:rational x := A + B, from D1
    obtain ⟨p, q, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A + (B : ℂ)))).mp hD1.2
    -- 2.2. calculation
    have s2_2 : A = ((p : ℂ) * (s : ℂ) - (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by
      calc A = (p : ℂ) / (q : ℂ) - (B : ℂ) := by have hz1 : (q : ℂ) ≠ 0 := (by norm_cast; positivity); linear_combination (norm := (field)) s2_1b
        _ = (p : ℂ) / (q : ℂ) - (r : ℂ) / (s : ℂ) := by (have h := congrArg (fun t : ℚ => (p : ℚ) / (q : ℚ) - t) s1b; push_cast at h ⊢; exact_mod_cast h)
        _ = ((p : ℂ) * (s : ℂ) - (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by have hz1 : (q : ℂ) ≠ 0 := (by norm_cast; positivity); have hz2 : (s : ℂ) ≠ 0 := (by norm_cast; positivity); field
    -- 2.3. def:rational x := A, from 2.2
    exact ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mpr ⟨p * s - r * q, q * s, mul_pos (s2_1a) (s1a), by (have h := s2_2; push_cast at h ⊢; exact h)⟩
  · skip
    intro hD2
    -- 2.4. obtain p, q: def:rational x := A, from D2
    obtain ⟨p, q, s2_4a, s2_4b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp hD2
    -- 2.5. membership, from D2
    -- 2.6. calculation
    have s2_6 : A + (B : ℂ) = ((p : ℂ) * (s : ℂ) + (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by
      calc A + (B : ℂ) = (p : ℂ) / (q : ℂ) + (B : ℂ) := congrArg (fun t : ℂ => t + (B : ℂ)) s2_4b
        _ = (p : ℂ) / (q : ℂ) + (r : ℂ) / (s : ℂ) := by (have h := congrArg (fun t : ℚ => (p : ℚ) / (q : ℚ) + t) s1b; push_cast at h ⊢; exact_mod_cast h)
        _ = ((p : ℂ) * (s : ℂ) + (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by have hz1 : (q : ℂ) ≠ 0 := (by norm_cast; positivity); have hz2 : (s : ℂ) ≠ 0 := (by norm_cast; positivity); field
    -- 2.7. def:rational x := A + B, from 2.6
    have s2_7 : ∃ m : ℚ, (m : ℂ) = A + (B : ℂ) := ((Parley.Items.Stdlib.Numbers.def_rational (x := A + (B : ℂ)))).mpr ⟨p * s + r * q, q * s, mul_pos (s2_4a) (s1a), by (have h := s2_6; push_cast at h ⊢; exact h)⟩
    -- 2.8. join 2.5, 2.7
    have s2_8 : True ∧ (∃ m : ℚ, (m : ℂ) = A + (B : ℂ)) := ⟨trivial, s2_7⟩
    exact ⟨trivial, (s2_8).2⟩

end Parley.Proofs.Setmm.ShiftByRational.ShiftByRational
