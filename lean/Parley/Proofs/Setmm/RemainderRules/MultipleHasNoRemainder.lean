module

public import AlgebraTactics
public import ArithTactics
public import Divisibility
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-rules.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder

theorem multiple_has_no_remainder (A : ℤ) (M : ℝ) (hH3 : M > 0) :
    LeanBridges.Divisibility.mod ((A : ℝ) * M) M = 0 := by
  -- 1. algebra
  have s1 : (A : ℝ) * M = M * (A : ℝ) := by parley_ring
  -- 2. calculation
  have r16_1 : (0 : ℤ) ≤ 0 := by parley_arith
  calc LeanBridges.Divisibility.mod ((A : ℝ) * M) M = LeanBridges.Divisibility.mod (M * (A : ℝ)) M := by parley_subst s1
    _ = LeanBridges.Divisibility.mod (0 : ℝ) M := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A)); parley_side)
    _ = 0 := by exact (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) (by parley_side) (by parley_side) (by parley_side))

end Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder
