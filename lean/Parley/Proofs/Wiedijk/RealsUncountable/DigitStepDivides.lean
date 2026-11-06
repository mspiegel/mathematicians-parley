module

public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides

theorem digit_step_divides (t : ℤ) :
    (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by
  -- 1. D2
  have s1 : (t + 1) % (10 : ℤ) = (t + 1) % (10 : ℤ) := by parley_side
  -- 2. mun:mod-congruent x := t + 1, n := 10
  have s2 : (t + 1) ≡ ((t + 1) % (10 : ℤ)) [ZMOD (10 : ℤ)] := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := t + 1) (n := (10 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := t + 1) (n := (10 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := t + 1) (n := (10 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := t + 1) (n := (10 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := t + 1) (n := (10 : ℤ)) (by parley_side)); parley_side)
  -- 3. def:congruent-mod n := 10, a := t + 1, b := (t + 1) mod 10, from 2
  have s3 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := t + 1) (b := (t + 1) % (10 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := t + 1) (b := (t + 1) % (10 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := t + 1) (b := (t + 1) % (10 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := t + 1) (b := (t + 1) % (10 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := t + 1) (b := (t + 1) % (10 : ℤ)))).mp (by parley_side); parley_side)
  -- 4. substitute s(t) = (t + 1) mod 10 (line 1) into line 3
  have s4 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by parley_subst_at s1 s3
  all_goals exact s4

end Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides
