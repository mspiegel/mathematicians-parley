module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides

theorem digit_step_divides (t : ℤ) :
    (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by
  -- 1. D2
  have s1 : (t + 1) % (10 : ℤ) = (t + 1) % (10 : ℤ) := rfl
  -- 2. mun:mod-congruent x := t + 1, n := 10
  have s2 : t + 1 ≡ (t + 1) % (10 : ℤ) [ZMOD (10 : ℤ)] := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := t + 1) (n := (10 : ℤ)) (by norm_num))
  -- 3. def:congruent-mod n := 10, a := t + 1, b := (t + 1) mod 10, from 2
  have s3 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := t + 1) (b := (t + 1) % (10 : ℤ)))).mp s2
  -- 4. substitute s(t) = (t + 1) mod 10 (line 1) into line 3
  exact s3

end Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides
