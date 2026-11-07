module

public import AlgebraTactics
public import Divisibility
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/gcd-add-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GcdAddMultiple.GcdAddMultiple

theorem gcd_add_multiple (K : ℤ) (M : ℤ) (hH2 : 0 < M) (N : ℤ) :
    (Int.gcd M N : ℤ) = (Int.gcd M (N + K * M) : ℤ) := by
  -- 1. thm:gcd-mod a := N + K·M, b := M
  have s1 : (Int.gcd ((N + K * M) % M) M : ℤ) = (Int.gcd (N + K * M) M : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side)); parley_side)
  -- 2. mun:mod-multiple r := N, m := M, q := K
  have s2 : (K * M + N) % M = N % M := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K)); parley_side)
  -- 3. substitute
  have s3 : (N + K * M) % M = N % M := by
    have c1 : K * M + N = N + K * M := by parley_ring
    have row1 : (N + K * M) % M = N % M := by parley_subst_at c1 s2
    exact row1
  -- 4. substitute (N + K·M) mod M = N mod M (line 3) into line 1
  have s4 : (Int.gcd (N % M) M : ℤ) = (Int.gcd (N + K * M) M : ℤ) := by parley_subst_at s3 s1
  -- 5. calculation
  have s5 : (Int.gcd M N : ℤ) = (Int.gcd M (N + K * M) : ℤ) := by
    calc (Int.gcd M N : ℤ) = (Int.gcd N M : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)); parley_side)
      _ = (Int.gcd (N % M) M : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)); parley_side)
      _ = (Int.gcd (N + K * M) M : ℤ) := by parley_side
      _ = (Int.gcd M (N + K * M) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M)); parley_side)
  all_goals exact s5

end Parley.Proofs.Setmm.GcdAddMultiple.GcdAddMultiple
