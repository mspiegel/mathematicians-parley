module

public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.DigitRange

theorem digit_range (t : ℤ) :
    (0 ≤ (t + 1) % (10 : ℤ) ∧ (t + 1) % (10 : ℤ) ≤ 9) := by
  -- 1. D2
  have s1 : (t + 1) % (10 : ℤ) = (t + 1) % (10 : ℤ) := by parley_side
  -- 2. mun:mod-less a := t + 1, b := 10
  have s2 : (t + 1) % (10 : ℤ) < 10 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := t + 1) (b := 10) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := t + 1) (b := 10) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := t + 1) (b := 10) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := t + 1) (b := 10) (by parley_side)); parley_side)
  -- 3. substitute s(t) = (t + 1) mod 10 (line 1) into line 2
  have s3 : (t + 1) % (10 : ℤ) < 10 := by parley_subst_at s1 s2
  -- 4. membership, from 1
  have s4 : 0 ≤ (t + 1) % (10 : ℤ) := by parley_side
  -- 5. mun:integer-step m := s(t), n := 10, from 3, 4
  have s5 : (t + 1) % (10 : ℤ) + 1 ≤ 10 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (t + 1) % (10 : ℤ)) (n := (10 : ℤ)) s3)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (t + 1) % (10 : ℤ)) (n := (10 : ℤ)) s3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (t + 1) % (10 : ℤ)) (n := (10 : ℤ)) s3) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (t + 1) % (10 : ℤ)) (n := (10 : ℤ)) s3); parley_side)
  -- 6. inequalities, from 4, 5
  have s6 : 0 ≤ (t + 1) % (10 : ℤ) ∧ (t + 1) % (10 : ℤ) ≤ 9 := by parley_side
  all_goals exact s6

end Parley.Proofs.Wiedijk.RealsUncountable.DigitRange
