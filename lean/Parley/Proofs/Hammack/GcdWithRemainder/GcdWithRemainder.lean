module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/gcd-with-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

theorem gcd_with_remainder (a : ℤ) (b : ℕ) (hH2 : 0 < b) (q : ℤ) (r : ℤ) (hH5 : a = q * (b : ℤ) + r) :
    (Int.gcd a (b : ℤ) : ℤ) = (Int.gcd r (b : ℤ) : ℤ) := by
  -- 1. calculation
  have s1 : a % (b : ℤ) = r % (b : ℤ) := by
    calc a % (b : ℤ) = (q * (b : ℤ) + r) % (b : ℤ) := by parley_subst hH5
      _ = r % (b : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); parley_side)
  -- 2. calculation
  have s2 : (Int.gcd a (b : ℤ) : ℤ) = (Int.gcd r (b : ℤ) : ℤ) := by
    calc (Int.gcd a (b : ℤ) : ℤ) = (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); parley_side)
      _ = (Int.gcd (r % (b : ℤ)) (b : ℤ) : ℤ) := by parley_subst s1
      _ = (Int.gcd r (b : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder
