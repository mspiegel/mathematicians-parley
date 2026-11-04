module

public import AlgebraTactics
public import Divisibility
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/gcd-minus-second-natural.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdMinusSecondNatural.GcdMinusSecondNatural

theorem gcd_minus_second_natural (a : ℤ) (b : ℕ) (hH2 : 0 < b) :
    (Int.gcd a (b : ℤ) : ℤ) = (Int.gcd (a - (b : ℤ)) (b : ℤ) : ℤ) := by
  -- 1. mun:mod-multiple r := a, m := b, q := −1
  have s1 : (-1 * (b : ℤ) + a) % (b : ℤ) = a % (b : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ))); parley_side)
  -- 2. substitute
  have s2 : (a - (b : ℤ)) % (b : ℤ) = a % (b : ℤ) := by
    have c1 : -1 * (b : ℤ) + a = a - (b : ℤ) := by parley_ring
    have row1 : (a - (b : ℤ)) % (b : ℤ) = a % (b : ℤ) := by parley_subst_at c1 s1
    exact row1
  -- 3. calculation
  have s3 : (Int.gcd a (b : ℤ) : ℤ) = (Int.gcd (a - (b : ℤ)) (b : ℤ) : ℤ) := by
    calc (Int.gcd a (b : ℤ) : ℤ) = (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); parley_side)
      _ = (Int.gcd ((a - (b : ℤ)) % (b : ℤ)) (b : ℤ) : ℤ) := by parley_subst s2
      _ = (Int.gcd (a - (b : ℤ)) (b : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - (b : ℤ)) (b := b) (by parley_side)); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.GcdMinusSecondNatural.GcdMinusSecondNatural
