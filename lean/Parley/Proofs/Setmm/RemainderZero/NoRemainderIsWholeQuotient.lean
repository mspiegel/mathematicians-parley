module

public import Divisibility
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.FloorBasics.FloorOfInteger

/-! Written from proofs/setmm/remainder-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderZero.NoRemainderIsWholeQuotient

theorem no_remainder_is_whole_quotient (A : ℝ) (B : ℝ) (hH3 : B > 0) :
    (LeanBridges.Divisibility.mod A B = 0 ↔ (∃ m : ℤ, (m : ℝ) = A / B)) := by
  -- 1. inequalities
  have s1 : B ≠ 0 := ne_of_gt (by linarith only [hH3])
  set q : ℤ := ⌊A / B⌋ with hD1
  -- 2. mun:mod-value a := A, b := B, from D1, H3
  have s2 : LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) hH3); push_cast at h; exact h)
  -- 3. both directions
  constructor
  · skip
    intro hC1
    -- 3.1. substitute A mod B = A − B·q (line 2) into C1
    have s3_1 : A - B * (q : ℝ) = 0 := Eq.subst (motive := (fun t : ℝ => t = 0)) s2 hC1
    -- 3.2. algebra, from 3.1
    have r33_1 : B ≠ 0 := by exact s1
    have s3_2 : A / B = (q : ℝ) := by have hz1 : B ≠ 0 := r33_1; linear_combination (norm := (field)) ((1) / ((B))) * s3_1
    -- 3.3. membership, from 3.2
    exact ⟨q, by exact_mod_cast (s3_2).symm⟩
  · skip
    intro hC2
    -- 3.4. calculation
    have s3_4 : (q : ℝ) = A / B := by
      calc (q : ℝ) = (⌊A / B⌋ : ℝ) := by simp (disch := omega) only [hD1]
        _ = A / B := by rw [← (by exact_mod_cast Classical.choose_spec hC2 : ((Classical.choose hC2 : ℤ) : ℝ) = A / B)]; (exact_mod_cast (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))))
    -- 3.5. calculation
    have r48_1 : B ≠ 0 := by exact s1
    calc LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := s2
      _ = 0 := by have hz1 : B ≠ 0 := r48_1; linear_combination (norm := (field)) (-B) * s3_4

end Parley.Proofs.Setmm.RemainderZero.NoRemainderIsWholeQuotient
