module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/consecutive-coprime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ConsecutiveCoprime.ConsecutiveCoprime

theorem consecutive_coprime (n : ℤ) (hH1 : 0 ≤ n) :
    (Int.gcd n (n + 1) : ℤ) = 1 := by
  -- 1. axi:excluded-middle P := n = 0
  have s1 : n = 0 ∨ n ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. calculation
    calc (Int.gcd n (n + 1) : ℤ) = (Int.gcd (0 : ℤ) (1 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (Int.gcd t (t + 1) : ℤ)) hC1; push_cast [zero_add] at h ⊢; all_goals exact_mod_cast h)
      _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ)))
  · skip
    -- 2.2. mun:nat0-nonzero m := n, from C2
    have s2_2 : 0 < n := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) hH1 hC2)
    -- 2.3. def:gcd a := n, b := n + 1, from 2.2
    have s2_3a : 0 < (Int.gcd n (n + 1) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) s2_2 (b := n + 1) (by parley_side))
    have s2_3b : (Int.gcd n (n + 1) : ℤ) ∣ n := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) s2_2 (b := n + 1) (by parley_side))
    have s2_3c : (Int.gcd n (n + 1) : ℤ) ∣ n + 1 := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) s2_2 (b := n + 1) (by parley_side))
    -- 2.4. mun:divides-difference d := gcd(n, n + 1), a := n + 1, b := n, from 2.3
    have s2_4 : (Int.gcd n (n + 1) : ℤ) ∣ n + 1 - n := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 1) : ℤ)) (a := n + 1) (b := n) s2_3c s2_3b)
    -- 2.5. substitute
    have s2_5 : (Int.gcd n (n + 1) : ℤ) ∣ (1 : ℤ) := by
      have c1 : n + 1 - n = 1 := by parley_ring
      have row1 : (Int.gcd n (n + 1) : ℤ) ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd n (n + 1) : ℤ) ∣ t)) c1 s2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 2.6. mun:divides-one d := gcd(n, n + 1), from 2.3, 2.5
    exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd n (n + 1) : ℤ)) s2_3a s2_5)

end Parley.Proofs.Hammack.ConsecutiveCoprime.ConsecutiveCoprime
