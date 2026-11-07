module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

/-! Written from proofs/hammack/congruent-same-gcd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentSameGcd.CongruentSameGcd

theorem congruent_same_gcd (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD n]) :
    (Int.gcd a n : ℤ) = (Int.gcd b n : ℤ) := by
  -- 1. def:congruent-mod, from H4
  have s1 : n ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. obtain k: def:divides d := n, n := a − b, from 1
  obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := n) (n := a - b))).mp (by parley_side)
  -- 3. algebra, from 2
  have s3 : a = k * n + b := by linear_combination (norm := parley_norm) s2
  -- 4. thm:gcd-with-remainder b := n, q := k, r := b, from 3
  have s4 : (Int.gcd a n : ℤ) = (Int.gcd b n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3) | exact_mod_cast ((Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3)).symm | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3); parley_int_power h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3); parley_side)
  all_goals exact s4

end Parley.Proofs.Hammack.CongruentSameGcd.CongruentSameGcd
