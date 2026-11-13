module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/eleven-divides-power-of-two-less-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ElevenDividesPowerOfTwoLessOne.ElevenDividesPowerOfTwoLessOne

theorem eleven_divides_power_of_two_less_one :
    (∃ n : ℤ, 0 < n ∧ (11 : ℤ) ∣ (2 ^ n.toNat - 1 : ℤ)) := by
  -- 1. arithmetic
  have s1 : (2 ^ 10 - 1 : ℤ) = 11 * 93 := by parley_arith
  -- 2. def:divides d := 11, n := 2^10 − 1, from 1
  have s2 : (11 : ℤ) ∣ (2 ^ 10 - 1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (11 : ℤ)) (n := (2 ^ 10 - 1 : ℤ)))).mpr ⟨(93 : ℤ), by norm_num⟩
  -- 3. exhibit, from 2
  exact ⟨(10 : ℤ), by norm_num, by simpa only [Int.reduceToNat] using s2⟩

end Parley.Proofs.Hammack.ElevenDividesPowerOfTwoLessOne.ElevenDividesPowerOfTwoLessOne
