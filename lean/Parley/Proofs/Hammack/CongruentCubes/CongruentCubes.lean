module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-cubes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentCubes.CongruentCubes

theorem congruent_cubes (a : ℤ) (b : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD (n : ℤ)]) :
    (a ^ 3) ≡ (b ^ 3) [ZMOD (n : ℤ)] := by
  -- 1. def:congruent-mod, from H4
  have s1 : (n : ℤ) ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. mun:divides-multiple e := n, a := a − b, x := a² + a·b + b², from 1
  have s2 : (n : ℤ) ∣ (a - b) * (a ^ 2 + a * b + b ^ 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (n : ℤ)) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (n : ℤ)) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (n : ℤ)) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (n : ℤ)) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (n : ℤ)) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (n : ℤ)) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) (by parley_side)); parley_side)
  -- 3. substitute
  have s3 : (n : ℤ) ∣ a ^ 3 - b ^ 3 := by
    have c1 : (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by parley_ring
    have row1 : (n : ℤ) ∣ a ^ 3 - b ^ 3 := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  have s4 : (a ^ 3) ≡ (b ^ 3) [ZMOD (n : ℤ)] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a ^ 3) (b := b ^ 3))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (n : ℤ)) (a := a ^ 3) (b := b ^ 3))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.CongruentCubes.CongruentCubes
