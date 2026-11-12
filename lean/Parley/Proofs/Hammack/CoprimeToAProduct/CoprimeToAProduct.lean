module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Wiedijk.Bezout.Bezout

/-! Written from proofs/hammack/coprime-to-a-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CoprimeToAProduct.CoprimeToAProduct

theorem coprime_to_a_product (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : (Int.gcd a c : ℤ) = 1) (hH5 : (Int.gcd b c : ℤ) = 1) :
    (Int.gcd (a * b) c : ℤ) = 1 := by
  -- 1. obtain x, y: thm:bezout b := c
  obtain ⟨x, y, s1⟩ := (Parley.Proofs.Wiedijk.Bezout.Bezout.bezout (a := a) hH1 (b := c) hH3)
  -- 2. substitute gcd(a, c) = 1 (H4) into line 1
  have s2 : a * x + c * y = 1 := by (have h := Eq.subst (motive := (fun t : ℤ => a * x + c * y = t)) hH4 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3. obtain u, v: thm:bezout a := b, b := c
  obtain ⟨u, v, s3⟩ := (Parley.Proofs.Wiedijk.Bezout.Bezout.bezout (a := b) hH2 (b := c) hH3)
  -- 4. substitute gcd(b, c) = 1 (H5) into line 3
  have s4 : b * u + c * v = 1 := by (have h := Eq.subst (motive := (fun t : ℤ => b * u + c * v = t)) hH5 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. calculation
  have s5 : a * b * (x * u) + c * (a * x * v + y * b * u + c * y * v) = 1 := by
    calc a * b * (x * u) + c * (a * x * v + y * b * u + c * y * v) = (a * x + c * y) * (b * u + c * v) := by parley_ring
      _ = 1 * (b * u + c * v) := by (have h := congrArg (fun t : ℤ => t * (b * u + c * v)) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 := by simpa only [one_mul] using s4
  -- 6. def:gcd a := a·b, b := c
  have s6a : 0 < (Int.gcd (a * b) c : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a * b) (mul_pos (hH1) (hH2)) (b := c) hH3)
  have s6b : (Int.gcd (a * b) c : ℤ) ∣ a * b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a * b) (mul_pos (hH1) (hH2)) (b := c) hH3)
  have s6c : (Int.gcd (a * b) c : ℤ) ∣ c := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a * b) (mul_pos (hH1) (hH2)) (b := c) hH3)
  -- 7. mun:divides-combination e := gcd(a·b, c), a := a·b, b := c, x := x·u, y := a·x·v + y·b·u + c·y·v, from 6
  have s7 : (Int.gcd (a * b) c : ℤ) ∣ a * b * (x * u) + c * (a * x * v + y * b * u + c * y * v) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd (a * b) c : ℤ)) (a := a * b) (b := c) (x := x * u) (y := a * x * v + y * b * u + c * y * v) s6b s6c)
  -- 8. substitute a·b·(x·u) + c·(a·x·v + y·b·u + c·y·v) = 1 (line 5) into line 7
  have s8 : (Int.gcd (a * b) c : ℤ) ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd (a * b) c : ℤ) ∣ t)) s5 s7; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 9. mun:divides-one d := gcd(a·b, c), from 6, 8
  exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd (a * b) c : ℤ)) s6a s8)

end Parley.Proofs.Hammack.CoprimeToAProduct.CoprimeToAProduct
