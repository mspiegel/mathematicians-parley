module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-same-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentSameRemainder.CongruentSameRemainder

theorem congruent_same_remainder (a : ℤ) (b : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD (n : ℤ)]) :
    a % (n : ℤ) = b % (n : ℤ) := by
  -- 1. def:congruent-mod, from H4
  have s1 : (n : ℤ) ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. obtain k: def:divides d := n, n := a − b, from 1
  obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (n : ℤ)) (n := a - b))).mp (by parley_side)
  -- 3. mun:mod-multiple r := b, m := n, q := k
  have s3 : (k * (n : ℤ) + b) % (n : ℤ) = b % (n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) (by parley_side) (q := k)); parley_side)
  -- 4. substitute
  have s4 : a % (n : ℤ) = b % (n : ℤ) := by
    have c1 : k * (n : ℤ) + b = a := by linear_combination (norm := parley_norm) (-1) * s2
    have row1 : a % (n : ℤ) = b % (n : ℤ) := by parley_subst_at c1 s3
    exact row1
  all_goals parley_side

end Parley.Proofs.Hammack.CongruentSameRemainder.CongruentSameRemainder
