module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.CoprimeDivides

theorem coprime_divides (x : ℤ) (c : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : n ∣ x * c) (hH5 : (Int.gcd c n : ℤ) = 1) :
    n ∣ x := by
  -- 1. obtain u, v: thm:bezout a := c, b := n
  obtain ⟨u, v, s1⟩ := (Parley.Items.Stdlib.Divisibility.thm_bezout (a := c) (b := n) (by parley_side))
  -- 2. substitute gcd(c, n) = 1 (H5) into line 1
  have s2 : c * u + n * v = 1 := by first | parley_subst_at hH5 s1 | (have e_nat : Int.gcd c n = 1 := by exact_mod_cast hH5; parley_subst_at e_nat s1)
  -- 3. mun:divides-self
  have s3 : n ∣ n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := n)); parley_side)
  -- 4. mun:divides-combination e := n, a := x·c, b := n, x := u, y := x·v, from H4, 3
  have s4 : n ∣ x * c * u + n * (x * v) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := x * c) (b := n) (x := u) (y := x * v) hH4 s3) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := x * c) (b := n) (x := u) (y := x * v) hH4 s3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := x * c) (b := n) (x := u) (y := x * v) hH4 s3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := x * c) (b := n) (x := u) (y := x * v) hH4 s3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := x * c) (b := n) (x := u) (y := x * v) hH4 s3); parley_side)
  -- 5. substitute
  have s5 : n ∣ x := by
    have c1 : x * c * u + n * (x * v) = x := by linear_combination (norm := parley_norm) (x) * s2
    have row1 : n ∣ x := by parley_subst_at c1 s4
    exact row1
  all_goals exact s5

end Parley.Stdlib.Divisibility.CoprimeDivides
