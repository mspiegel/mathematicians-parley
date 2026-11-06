module

public import ArithTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/eleven-divides-power-of-two-less-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ElevenDividesPowerOfTwoLessOne.ElevenDividesPowerOfTwoLessOne

theorem eleven_divides_power_of_two_less_one :
    (∃ n : ℤ, 0 < n ∧ (11 : ℤ) ∣ (2 ^ n.toNat - 1 : ℤ)) := by
  -- 1. arithmetic
  have s1 : (2 ^ 10 - 1 : ℤ) = 11 * 93 := by parley_arith
  -- 2. def:divides d := 11, n := 2^10 − 1, from 1
  have s2 : (11 : ℤ) ∣ (2 ^ 10 - 1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (11 : ℤ)) (n := (2 ^ 10 - 1 : ℤ)))).mpr ⟨(93 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (11 : ℤ)) (n := (2 ^ 10 - 1 : ℤ)))).mpr ⟨(93 : ℤ), by parley_side⟩; parley_side)
  -- 3. exhibit, from 2
  have s3 : ∃ n : ℤ, 0 < n ∧ (11 : ℤ) ∣ (2 ^ n.toNat - 1 : ℤ) := ⟨(10 : ℤ), by parley_side, by parley_side⟩
  all_goals exact s3

end Parley.Proofs.Hammack.ElevenDividesPowerOfTwoLessOne.ElevenDividesPowerOfTwoLessOne
