module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdOne

theorem gcd_one (a : ℤ) :
    (Int.gcd a (1 : ℤ) : ℤ) = 1 := by
  -- 1. mun:divisibility-gcd-one
  have s1 : (Int.gcd a (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdOne
