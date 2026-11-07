module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-divides-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDividesProduct.PrimeDividesProduct

set_option maxHeartbeats 400000 in
theorem prime_divides_product (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (M : ℤ) (N : ℤ) :
    (P ∣ M * N ↔ P ∣ M ∨ P ∣ N) := by
  -- 1. algebra
  have s1 : M * N = N * M := by parley_ring
  -- 2. both directions
  have s2 : P ∣ M * N ↔ P ∣ M ∨ P ∣ N := by
    constructor
    · skip
      intro hD1
      -- 2.1. axi:excluded-middle P := P divides M
      have s2_1 : P ∣ M ∨ ¬ P ∣ M := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P ∣ M))
      -- 2.2. cases, from 2.1
      have s2_2 : P ∣ M ∨ P ∣ N := by
        rcases s2_1 with hC1 | hC2
        · skip
          -- 2.2.1. mun:or-left P := P divides M, Q := P divides N, from C1
          have s2_2_1 : P ∣ M ∨ P ∣ N := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P ∣ M) (Q := P ∣ N) hC1)
          all_goals parley_side
        · skip
          -- 2.2.2. calculation
          have s2_2_2 : (Int.gcd M P : ℤ) = 1 := by
            calc (Int.gcd M P : ℤ) = (Int.gcd P M : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P))
              _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2)
          -- 2.2.3. substitute M·N = N·M (line 1) into D1
          have s2_2_3 : P ∣ N * M := by parley_subst_at s1 hD1
          -- 2.2.4. thm:coprime-divides x := N, c := M, n := P, from 2.2.2, 2.2.3
          have s2_2_4 : P ∣ N := by exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := N) (c := M) (n := P) (by parley_side) s2_2_3 s2_2_2)
          -- 2.2.5. mun:or-right P := P divides M, Q := P divides N, from 2.2.4
          have s2_2_5 : P ∣ M ∨ P ∣ N := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P ∣ M) (Q := P ∣ N) s2_2_4)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 2.3. cases, from D2
      have s2_3 : P ∣ M * N := by
        rcases hD2 with hC3 | hC4
        · skip
          -- 2.3.1. mun:divides-multiple e := P, a := M, x := N, from C3
          have s2_3_1 : P ∣ M * N := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := M) (x := N) hC3)
          all_goals parley_side
        · skip
          -- 2.3.2. mun:divides-multiple e := P, a := N, x := M, from C4
          have s2_3_2 : P ∣ N * M := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := N) (x := M) hC4)
          -- 2.3.3. substitute N·M = M·N (line 1) into line 2.3.2
          have s2_3_3 : P ∣ M * N := by parley_subst_at s1 s2_3_2
          all_goals parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.PrimeDividesProduct.PrimeDividesProduct
