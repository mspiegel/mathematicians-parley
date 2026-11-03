module

public import Divisibility
public import Tactics
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
  have s2 : LeanBridges.Divisibility.mod ((A : ℝ) * M) M = 0 := by
    calc LeanBridges.Divisibility.mod ((A : ℝ) * M) M = LeanBridges.Divisibility.mod (M * (A : ℝ)) M := by parley_subst s1
      _ = LeanBridges.Divisibility.mod (0 : ℝ) M := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A)); parley_side)
      _ = 0 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by parley_side) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder
