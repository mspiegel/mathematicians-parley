module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/divides-square-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesSquareDifference.DividesSquareDifference

theorem divides_square_difference (a : ℤ) (b : ℤ) (c : ℤ) (hH4 : a ∣ b) (hH5 : a ∣ b ^ 2 - c) :
    a ∣ c := by
  -- 1. mun:divides-multiple e := a, a := b, x := b, from H4
  have s1 : a ∣ b * b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := a) (a := b) (x := b) hH4) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := a) (a := b) (x := b) hH4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := a) (a := b) (x := b) hH4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := a) (a := b) (x := b) hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := a) (a := b) (x := b) hH4); parley_side)
  -- 2. substitute
  have s2 : a ∣ b ^ 2 := by
    have c1 : b * b = b ^ 2 := by parley_ring
    have row1 : a ∣ b ^ 2 := by parley_subst_at c1 s1
    exact row1
  -- 3. mun:divides-difference d := a, a := b², b := b² − c, from H5, 2
  have s3 : a ∣ b ^ 2 - (b ^ 2 - c) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := a) (a := b ^ 2) (b := b ^ 2 - c) s2 hH5) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := a) (a := b ^ 2) (b := b ^ 2 - c) s2 hH5)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := a) (a := b ^ 2) (b := b ^ 2 - c) s2 hH5) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := a) (a := b ^ 2) (b := b ^ 2 - c) s2 hH5) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := a) (a := b ^ 2) (b := b ^ 2 - c) s2 hH5); parley_side)
  -- 4. substitute
  have s4 : a ∣ c := by
    have c1 : b ^ 2 - (b ^ 2 - c) = c := by parley_ring
    have row1 : a ∣ c := by parley_subst_at c1 s3
    exact row1
  all_goals exact s4

end Parley.Proofs.Hammack.DividesSquareDifference.DividesSquareDifference
