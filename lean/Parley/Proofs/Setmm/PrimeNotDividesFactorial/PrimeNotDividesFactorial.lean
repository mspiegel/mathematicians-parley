module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-not-divides-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeNotDividesFactorial.PrimeNotDividesFactorial

theorem prime_not_divides_factorial (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (N : ℤ) (hH3 : 0 ≤ N) (hH4 : N < P) :
    ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by
  -- 1. def:prime p := P, from H2
  have s1 : P > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) hH1)).mp hH2).1
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℤ, 0 < k → k < P → ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      intro hB
      -- 2.1. contradiction
      intro hS1
      -- 2.1.1. def:factorial
      have s2_1_1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
      -- 2.1.2. substitute 1! = 1 (line 2.1.1) into S1
      have s2_1_2 : P ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => P ∣ t)) s2_1_1 hS1; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 2.1.3. mun:divides-one d := P, from 2.1.2
      have s2_1_3 : P = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) hH1 s2_1_2)
      -- 2.1.4. inequalities
      have s2_1_4 : P ≠ 1 := by parley_side
      exact s2_1_4 s2_1_3
    | succ k hK hIH =>
      intro hA
      -- 2.2. contradiction
      intro hS2
      -- 2.2.1. def:factorial n := k
      have s2_2_1 : (LeanBridges.Counting.factorial (k + 1) : ℤ) = (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK)))
      -- 2.2.2. substitute (k + 1)! = k!·(k + 1) (line 2.2.1) into S2
      have s2_2_2 : P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by (have h := Eq.subst (motive := (fun t : ℤ => P ∣ t)) s2_2_1 hS2; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 2.2.3. thm:prime-divides-product m := k!, n := k + 1, from H2
      have s2_2_3 : P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1) ↔ P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1 := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) hH1 hH2 (m := (LeanBridges.Counting.factorial k : ℤ)) (n := k + 1))
      -- 2.2.4. mun:iff-from-left, from 2.2.2, 2.2.3
      have s2_2_4 : P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1 := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := P ∣ (LeanBridges.Counting.factorial k : ℤ) * (k + 1)) (Q := P ∣ (LeanBridges.Counting.factorial k : ℤ) ∨ P ∣ k + 1) s2_2_3 s2_2_2)
      -- 2.2.5. inequalities, from A
      have s2_2_5 : k < P := by parley_order
      -- 2.2.6. mun:modus-ponens, from IH, 2.2.5
      have s2_2_6 : ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := k < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ)) hIH s2_2_5)
      -- 2.2.7. cases, from 2.2.4
      have s2_2_7 : P ≤ k + 1 := by
        rcases s2_2_4 with hC1 | hC2
        · skip
          -- 2.2.7.1. restate 2.2.6
          have s2_2_7_1 : ¬ P ∣ (LeanBridges.Counting.factorial k : ℤ) := by exact s2_2_6
          exact absurd hC1 s2_2_7_1
        · skip
          -- 2.2.7.2. mun:divides-le e := P, m := k + 1, from C2
          exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := P) hH1 (m := k + 1) (by parley_side) hC2)
      -- 2.2.8. inequalities, from 2.2.7
      have s2_2_8 : ¬ k + 1 < P := by parley_side
      exact s2_2_8 hA
  -- 3. axi:excluded-middle P := N = 0
  have s3 : N = 0 ∨ N ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := N = 0))
  -- 4. cases, from 3
  rcases s3 with hC3 | hC4
  · skip
    -- 4.1. arithmetic
    have s4_1 : (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 := by parley_arith
    -- 4.2. substitute N = 0 (C3) into line 4.1
    have s4_2 : (LeanBridges.Counting.factorial N : ℤ) = 1 := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ) = 1)) hC3.symm s4_1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 4.3. contradiction
    intro hS3
    -- 4.3.1. substitute N! = 1 (line 4.2) into S3
    have s4_3_1 : P ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => P ∣ t)) s4_2 hS3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 4.3.2. mun:divides-one d := P, from 4.3.1
    have s4_3_2 : P = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) hH1 s4_3_1)
    -- 4.3.3. inequalities
    have s4_3_3 : P ≠ 1 := by parley_side
    exact s4_3_3 s4_3_2
  · skip
    -- 4.4. mun:nat0-nonzero m := N, from C4
    have s4_4 : 0 < N := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := N) hH3 hC4)
    -- 4.5. instantiate k := N in line 2, from 4.4
    have s4_5 : N < P → ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ) := by exact (s2 N s4_4)
    -- 4.6. mun:modus-ponens, from H4, 4.5
    exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := N < P) (Q := ¬ P ∣ (LeanBridges.Counting.factorial N : ℤ)) s4_5 hH4)

end Parley.Proofs.Setmm.PrimeNotDividesFactorial.PrimeNotDividesFactorial
