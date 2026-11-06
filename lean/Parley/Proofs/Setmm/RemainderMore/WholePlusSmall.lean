module

public import AlgebraTactics
public import Divisibility
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderMore.WholePlusSmall

theorem whole_plus_small (A : ℤ) (hH1 : 0 ≤ A) (M : ℤ) (hH2 : 0 < M) (hH3 : A < M) :
    (M + A) % M = A := by
  -- 1. algebra
  have s1 : M + A = A + M := by parley_ring
  -- 2. calculation
  have s2 : (M + A) % M = A := by
    calc (M + A) % M = (A + M) % M := by parley_subst s1
      _ = A % M := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ)))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by parley_side) (K := (1 : ℤ))); parley_side)
      _ = A := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.RemainderMore.WholePlusSmall
