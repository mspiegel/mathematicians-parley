module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.CoprimeDivides

theorem coprime_divides (x : ℤ) (c : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : n ∣ x * c) (hH5 : (Int.gcd c n : ℤ) = 1) :
    n ∣ x := by
  -- 1. obtain u, v: thm:bezout a := c, b := n
  obtain ⟨u, v, s1⟩ := (Parley.Items.Stdlib.Divisibility.thm_bezout (a := c) (b := n) (by parley_side))
  -- 2. substitute gcd(c, n) = 1 (H5) into line 1
  have s2 : c * u + n * v = 1 := by (have h := Eq.subst (motive := (fun t : ℤ => c * u + n * v = t)) hH5 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3. mun:divides-self
  have s3 : n ∣ n := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := n))
  -- 4. mun:divides-combination e := n, a := x·c, b := n, x := u, y := x·v, from H4, 3
  have s4 : n ∣ x * c * u + n * (x * v) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := x * c) (b := n) (x := u) (y := x * v) hH4 s3)
  -- 5. substitute
  have c1 : x * c * u + n * (x * v) = x := by linear_combination (norm := parley_norm) (x) * s2
  have row1 : n ∣ x := by parley_subst_at c1 s4
  exact row1

end Parley.Stdlib.Divisibility.CoprimeDivides
