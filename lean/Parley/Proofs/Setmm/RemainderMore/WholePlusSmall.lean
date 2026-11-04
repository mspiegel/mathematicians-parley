module

public import AlgebraTactics
public import Divisibility
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderMore.WholePlusSmall

theorem whole_plus_small (A : ℕ) (M : ℕ) (hH2 : 0 < M) (hH3 : (A : ℤ) < (M : ℤ)) :
    ((M : ℤ) + (A : ℤ)) % (M : ℤ) = (A : ℤ) := by
  -- 1. algebra
  have s1 : (M : ℤ) + (A : ℤ) = (A : ℤ) + (M : ℤ) := by parley_ring
  -- 2. calculation
  have s2 : ((M : ℤ) + (A : ℤ)) % (M : ℤ) = (A : ℤ) := by
    calc ((M : ℤ) + (A : ℤ)) % (M : ℤ) = ((A : ℤ) + (M : ℤ)) % (M : ℤ) := by parley_subst s1
      _ = (A : ℤ) % (M : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ)))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); parley_side)
      _ = (A : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.RemainderMore.WholePlusSmall
