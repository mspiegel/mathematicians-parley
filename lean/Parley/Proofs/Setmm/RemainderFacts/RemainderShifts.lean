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
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.FloorBasics.FloorAddInteger

/-! Written from proofs/setmm/remainder-facts.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

theorem remainder_shifts (X : ℝ) (M : ℝ) (hH3 : M > 0) (K : ℤ) :
    LeanBridges.Divisibility.mod (X + M * (K : ℝ)) M = LeanBridges.Divisibility.mod X M := by
  -- 1. mun:floor-integer x := X/M
  have r16_1 : M ≠ 0 := ne_of_gt (by linarith only [hH3])
  -- 2. thm:floor-add-integer A := X/M, N := K
  have r20_1 : M ≠ 0 := ne_of_gt (by linarith only [hH3])
  have s2 : ⌊X / M + (K : ℝ)⌋ = ⌊X / M⌋ + K := by exact (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := X / M) (N := K))
  -- 3. substitute
  have r24_1 : M ≠ 0 := ne_of_gt (by linarith only [hH3])
  have s3 : ⌊(X + M * (K : ℝ)) / M⌋ = ⌊X / M⌋ + K := by
    have c1 : X / M + (K : ℝ) = (X + M * (K : ℝ)) / M := by field
    have row1 : ⌊(X + M * (K : ℝ)) / M⌋ = ⌊X / M⌋ + K := Eq.subst (motive := (fun t : ℝ => ⌊t⌋ = ⌊X / M⌋ + K)) c1 s2
    exact row1
  -- 4. calculation
  calc LeanBridges.Divisibility.mod (X + M * (K : ℝ)) M = X + M * (K : ℝ) - M * (⌊(X + M * (K : ℝ)) / M⌋ : ℝ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := X + M * (K : ℝ)) (b := M) hH3)
    _ = X + M * (K : ℝ) - M * ((⌊X / M⌋ : ℝ) + (K : ℝ)) := by
        have e_w : (⌊(X + M * (K : ℝ)) / M⌋ : ℝ) = (⌊X / M⌋ : ℝ) + (K : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s3; push_cast at h ⊢; linear_combination h
        exact congrArg (fun t : ℝ => X + M * (K : ℝ) - M * t) e_w
    _ = X - M * (⌊X / M⌋ : ℝ) := by field
    _ = LeanBridges.Divisibility.mod X M := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := X) (b := M) hH3).symm

end Parley.Proofs.Setmm.RemainderFacts.RemainderShifts
