module

public import Divisibility
public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor
public import Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderReal.RemainderIsReal

/-! Written from proofs/setmm/remainder-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderMore.RemainderUnderALargerDivisor

theorem remainder_under_a_larger_divisor (A : ℝ) (B : ℝ) (C : ℝ) (hH4 : B > 0) (hH5 : C > 0) (hH6 : B ≤ C) :
    LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A B) C = LeanBridges.Divisibility.mod A B := by
  -- 1. thm:remainder-is-real, from H4
  -- 2. thm:remainder-nonnegative, from H4
  have s2 : 0 ≤ LeanBridges.Divisibility.mod A B := by first | linarith [(Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative.remainder_nonnegative (A := A) (B := B) hH4)] | (have h := (Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative.remainder_nonnegative (A := A) (B := B) hH4); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative.remainder_nonnegative (A := A) (B := B) hH4) | (have h := (Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative.remainder_nonnegative (A := A) (B := B) hH4); parley_side)
  -- 3. thm:remainder-below-divisor, from H4
  have s3 : LeanBridges.Divisibility.mod A B < B := by first | linarith [(Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor.remainder_below_divisor (A := A) (B := B) hH4)] | (have h := (Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor.remainder_below_divisor (A := A) (B := B) hH4); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor.remainder_below_divisor (A := A) (B := B) hH4) | (have h := (Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor.remainder_below_divisor (A := A) (B := B) hH4); parley_side)
  -- 4. transitivity, from 3, H6
  have s4 : LeanBridges.Divisibility.mod A B < C := by parley_order
  -- 5. thm:remainder-of-small A := A mod B, B := C, from H5, 1, 2, 4
  have s5 : LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A B) C = LeanBridges.Divisibility.mod A B := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4)).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) hH5 s2 s4); parley_side)
  all_goals exact s5

end Parley.Proofs.Setmm.RemainderMore.RemainderUnderALargerDivisor
