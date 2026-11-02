module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/square-congruent-one-mod-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareCongruentOneModFive.SquareCongruentOneModFive

theorem square_congruent_one_mod_five (a : ℤ) (hH2 : a ≡ (1 : ℤ) [ZMOD (5 : ℤ)]) :
    (a ^ 2) ≡ (1 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. def:congruent-mod, from H2
  have s1 : (5 : ℤ) ∣ a - 1 := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side); parley_side)
  -- 2. mun:divides-multiple e := 5, a := a − 1, x := a + 1, from 1
  have s2 : (5 : ℤ) ∣ (a - 1) * (a + 1) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) (by parley_side)); parley_side)
  -- 3. substitute
  have s3 : (5 : ℤ) ∣ a ^ 2 - 1 := by
    have c1 : (a - 1) * (a + 1) = a ^ 2 - 1 := by parley_ring
    have row1 : (5 : ℤ) ∣ a ^ 2 - 1 := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  have s4 : (a ^ 2) ≡ (1 : ℤ) [ZMOD (5 : ℤ)] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a ^ 2) (b := (1 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a ^ 2) (b := (1 : ℤ)))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.SquareCongruentOneModFive.SquareCongruentOneModFive
