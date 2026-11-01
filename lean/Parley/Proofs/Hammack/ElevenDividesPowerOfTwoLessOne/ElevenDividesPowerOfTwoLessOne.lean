module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/eleven-divides-power-of-two-less-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ElevenDividesPowerOfTwoLessOne.ElevenDividesPowerOfTwoLessOne

theorem eleven_divides_power_of_two_less_one :
    (∃ n : ℕ, 0 < n ∧ (11 : ℤ) ∣ (2 ^ n - 1 : ℤ)) := by
  -- 1. arithmetic
  have s1 : (2 ^ 10 - 1 : ℤ) = 11 * 93 := by norm_num
  -- 2. def:divides d := 11, n := 2^10 − 1, from 1
  have s2 : (11 : ℤ) ∣ (2 ^ 10 - 1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (11 : ℤ)) (n := (2 ^ 10 - 1 : ℤ)))).mpr ⟨(93 : ℤ), by parley_side⟩
  -- 3. exhibit, from 2
  have s3 : ∃ n : ℕ, 0 < n ∧ (11 : ℤ) ∣ (2 ^ n - 1 : ℤ) := ⟨10, by parley_side, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.ElevenDividesPowerOfTwoLessOne.ElevenDividesPowerOfTwoLessOne
