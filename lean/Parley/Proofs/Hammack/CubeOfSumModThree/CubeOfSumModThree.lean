module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/cube-of-sum-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeOfSumModThree.CubeOfSumModThree

theorem cube_of_sum_mod_three (a : ℤ) (b : ℤ) :
    ((a + b) ^ 3) ≡ (a ^ 3 + b ^ 3) [ZMOD (3 : ℤ)] := by
  -- 1. algebra
  have s1 : (a + b) ^ 3 - (a ^ 3 + b ^ 3) = 3 * (a ^ 2 * b + a * b ^ 2) := by ring
  -- 2. def:divides d := 3, n := (a + b)³ − (a³ + b³), from 1
  have s2 : (3 : ℤ) ∣ (a + b) ^ 3 - (a ^ 3 + b ^ 3) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (a + b) ^ 3 - (a ^ 3 + b ^ 3)))).mpr ⟨a ^ 2 * b + a * b ^ 2, by parley_side⟩
  -- 3. def:congruent-mod n := 3, from 2
  have s3 : ((a + b) ^ 3) ≡ (a ^ 3 + b ^ 3) [ZMOD (3 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (a + b) ^ 3) (b := a ^ 3 + b ^ 3))).mpr (by parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.CubeOfSumModThree.CubeOfSumModThree
