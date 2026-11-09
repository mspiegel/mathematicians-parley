module

public import AlgebraTactics
public import Divisibility
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.FloorBasics.FloorAddInteger

/-! Written from proofs/setmm/remainder-facts.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

theorem remainder_shifts (X : ℝ) (M : ℝ) (hH3 : M > 0) (K : ℤ) :
    LeanBridges.Divisibility.mod (X + M * (K : ℝ)) M = LeanBridges.Divisibility.mod X M := by
  -- 1. mun:floor-integer x := X/M
  have r16_1 : M ≠ 0 := by parley_side
  -- 2. thm:floor-add-integer A := X/M, N := K
  have r20_1 : M ≠ 0 := by parley_side
  have s2 : ⌊X / M + (K : ℝ)⌋ = ⌊X / M⌋ + K := by exact (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := X / M) (N := K))
  -- 3. substitute
  have r24_1 : M ≠ 0 := by parley_side
  have s3 : ⌊(X + M * (K : ℝ)) / M⌋ = ⌊X / M⌋ + K := by
    have c1 : X / M + (K : ℝ) = (X + M * (K : ℝ)) / M := by parley_ring
    have row1 : ⌊(X + M * (K : ℝ)) / M⌋ = ⌊X / M⌋ + K := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  calc LeanBridges.Divisibility.mod (X + M * (K : ℝ)) M = X + M * (K : ℝ) - M * (⌊(X + M * (K : ℝ)) / M⌋ : ℝ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := X + M * (K : ℝ)) (b := M) hH3)
    _ = X + M * (K : ℝ) - M * ((⌊X / M⌋ : ℝ) + (K : ℝ)) := by
        have s3_w : (⌊(X + M * (K : ℝ)) / M⌋ : ℝ) = (⌊X / M⌋ : ℝ) + (K : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s3; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s3_w | parley_subst s3
    _ = X - M * (⌊X / M⌋ : ℝ) := by parley_ring
    _ = LeanBridges.Divisibility.mod X M := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := X) (b := M) hH3).symm

end Parley.Proofs.Setmm.RemainderFacts.RemainderShifts
