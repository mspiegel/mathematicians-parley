module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/a-membership-a-bare-from-builds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMembershipABareFromBuilds.AProductMembershipFromALine

theorem a_product_membership_from_a_line (f : ℤ → ℤ) (hH1 : Set.MapsTo f {n : ℤ | 0 < n} {n : ℤ | 0 < n}) (a : ℤ) (hH2 : 0 < a) (c : ℤ) (x : ℤ) (y : ℤ) (hH6 : c * f a ∣ x) (hH7 : c * f a ∣ y) :
    c * f a ∣ (Int.gcd x y : ℤ) := by
  -- 1. membership, from H1
  have s1 : 0 < f a := by parley_set_side
  -- 2. thm:divides-gcd d := c·f(a), a := x, b := y, from H6, H7
  have s2 : c * f a ∣ (Int.gcd x y : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := c * f a) (a := x) (b := y) hH6 hH7) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := c * f a) (a := x) (b := y) hH6 hH7)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := c * f a) (a := x) (b := y) hH6 hH7) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := c * f a) (a := x) (b := y) hH6 hH7) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := c * f a) (a := x) (b := y) hH6 hH7); parley_set_side)
  all_goals exact s2

end Parley.Tests.Elaborator.AMembershipABareFromBuilds.AProductMembershipFromALine
