module

public import AlgebraTactics
public import SubstTactics
public import Tactics
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
  have s1 : n = 0 ∨ n ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0)); parley_side)
  -- 2. cases, from 1
  have s2 : (Int.gcd n (n + 1) : ℤ) = 1 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. calculation
      have s2_1 : (Int.gcd n (n + 1) : ℤ) = 1 := by
        calc (Int.gcd n (n + 1) : ℤ) = (Int.gcd (0 : ℤ) (1 : ℤ) : ℤ) := by parley_subst hC1
          _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ)))
      all_goals parley_side
    · skip
      -- 2.2. mun:nat0-nonzero m := n, from C2
      have s2_2 : 0 < n := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side) hC2)
      -- 2.3. def:gcd a := n, b := n + 1, from 2.2
      have s2_3a : 0 < (Int.gcd n (n + 1) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side))
      have s2_3b : (Int.gcd n (n + 1) : ℤ) ∣ n := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side))
      have s2_3c : (Int.gcd n (n + 1) : ℤ) ∣ n + 1 := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side))
      -- 2.4. mun:divides-difference d := gcd(n, n + 1), a := n + 1, b := n, from 2.3
      have s2_4 : (Int.gcd n (n + 1) : ℤ) ∣ n + 1 - n := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 1) : ℤ)) (a := n + 1) (b := n) s2_3c s2_3b)
      -- 2.5. substitute
      have s2_5 : (Int.gcd n (n + 1) : ℤ) ∣ (1 : ℤ) := by
        have c1 : n + 1 - n = 1 := by parley_ring
        have row1 : (Int.gcd n (n + 1) : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s2_4
        exact row1
      -- 2.6. mun:divides-one d := gcd(n, n + 1), from 2.3, 2.5
      have s2_6 : (Int.gcd n (n + 1) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd n (n + 1) : ℤ)) (by parley_side) s2_5)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.ConsecutiveCoprime.ConsecutiveCoprime
