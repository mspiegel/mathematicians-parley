module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

/-! Written from proofs/hammack/congruent-same-gcd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentSameGcd.CongruentSameGcd

theorem congruent_same_gcd (a : ℤ) (b : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD (n : ℤ)]) :
    (Int.gcd a (n : ℤ) : ℤ) = (Int.gcd b (n : ℤ) : ℤ) := by
  -- 1. def:congruent-mod, from H4
  have s1 : (n : ℤ) ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. obtain k: def:divides d := n, n := a − b, from 1
  obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (n : ℤ)) (n := a - b))).mp (by parley_side)
  -- 3. algebra, from 2
  have s3 : a = k * (n : ℤ) + b := by linear_combination (norm := parley_norm) s2
  -- 4. thm:gcd-with-remainder b := n, q := k, r := b, from 3
  have s4 : (Int.gcd a (n : ℤ) : ℤ) = (Int.gcd b (n : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.CongruentSameGcd.CongruentSameGcd
