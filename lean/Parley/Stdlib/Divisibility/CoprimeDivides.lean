module

public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.CoprimeDivides

theorem coprime_divides (x : ℤ) (c : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : (n : ℤ) ∣ x * c) (hH5 : (Int.gcd c (n : ℤ) : ℤ) = 1) :
    (n : ℤ) ∣ x := by
  -- 1. obtain u, v: thm:bezout a := c, b := n
  obtain ⟨u, v, s1⟩ := (Parley.Items.Stdlib.Divisibility.thm_bezout (a := c) (b := n) (by parley_side))
  -- 2. substitute gcd(c, n) = 1 (H5) into line 1
  have s2 : c * u + (n : ℤ) * v = 1 := by parley_subst_at hH5 s1
  -- 3. mun:divides-self
  have s3 : (n : ℤ) ∣ (n : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (n : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (n : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (n : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (n : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (n : ℤ))); parley_side)
  -- 4. mun:divides-combination e := n, a := x·c, b := n, x := u, y := x·v, from H4, 3
  have s4 : (n : ℤ) ∣ x * c * u + (n : ℤ) * (x * v) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (n : ℤ)) (a := x * c) (b := (n : ℤ)) (x := u) (y := x * v) hH4 s3) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (n : ℤ)) (a := x * c) (b := (n : ℤ)) (x := u) (y := x * v) hH4 s3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (n : ℤ)) (a := x * c) (b := (n : ℤ)) (x := u) (y := x * v) hH4 s3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (n : ℤ)) (a := x * c) (b := (n : ℤ)) (x := u) (y := x * v) hH4 s3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (n : ℤ)) (a := x * c) (b := (n : ℤ)) (x := u) (y := x * v) hH4 s3); parley_side)
  -- 5. substitute
  have s5 : (n : ℤ) ∣ x := by
    have c1 : x * c * u + (n : ℤ) * (x * v) = x := by linear_combination (norm := parley_norm) (x) * s2
    have row1 : (n : ℤ) ∣ x := by parley_subst_at c1 s4
    exact row1
  all_goals exact s5

end Parley.Stdlib.Divisibility.CoprimeDivides
