module

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

/-! Written from proofs/hammack/gcd-with-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

theorem gcd_with_remainder (a : ℤ) (b : ℤ) (hH2 : 0 < b) (q : ℤ) (r : ℤ) (hH5 : a = q * b + r) :
    (Int.gcd a b : ℤ) = (Int.gcd r b : ℤ) := by
  -- 1. calculation
  have s1 : a % b = r % b := by
    calc a % b = (q * b + r) % b := by parley_subst hH5
      _ = r % b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q)); parley_side)
  -- 2. calculation
  have s2 : (Int.gcd a b : ℤ) = (Int.gcd r b : ℤ) := by
    calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); parley_side)
      _ = (Int.gcd (r % b) b : ℤ) := by parley_subst s1
      _ = (Int.gcd r b : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder
