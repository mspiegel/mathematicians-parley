module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
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
      have s2_1 : P ∣ M ∨ ¬ P ∣ M := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P ∣ M)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P ∣ M))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P ∣ M)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P ∣ M)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := P ∣ M)); parley_side)
      -- 2.2. cases, from 2.1
      have s2_2 : P ∣ M ∨ P ∣ N := by
        rcases s2_1 with hC1 | hC2
        · skip
          -- 2.2.1. mun:or-left P := P divides M, Q := P divides N, from C1
          have s2_2_1 : P ∣ M ∨ P ∣ N := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P ∣ M) (Q := P ∣ N) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := P ∣ M) (Q := P ∣ N) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P ∣ M) (Q := P ∣ N) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P ∣ M) (Q := P ∣ N) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P ∣ M) (Q := P ∣ N) hC1); parley_side)
          all_goals parley_side
        · skip
          -- 2.2.2. calculation
          have s2_2_2 : (Int.gcd M P : ℤ) = 1 := by
            calc (Int.gcd M P : ℤ) = (Int.gcd P M : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := M) (b := P)); parley_side)
              _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := P) (by parley_side) hH2 (a := M) hC2); parley_side)
          -- 2.2.3. substitute M·N = N·M (line 1) into D1
          have s2_2_3 : P ∣ N * M := by parley_subst_at s1 hD1
          -- 2.2.4. thm:coprime-divides x := N, c := M, n := P, from 2.2.2, 2.2.3
          have s2_2_4 : P ∣ N := by first | exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := N) (c := M) (n := P) (by parley_side) s2_2_3 s2_2_2) | exact ((Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := N) (c := M) (n := P) (by parley_side) s2_2_3 s2_2_2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := N) (c := M) (n := P) (by parley_side) s2_2_3 s2_2_2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := N) (c := M) (n := P) (by parley_side) s2_2_3 s2_2_2) | (have h := (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := N) (c := M) (n := P) (by parley_side) s2_2_3 s2_2_2); parley_side)
          -- 2.2.5. mun:or-right P := P divides M, Q := P divides N, from 2.2.4
          have s2_2_5 : P ∣ M ∨ P ∣ N := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P ∣ M) (Q := P ∣ N) s2_2_4) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := P ∣ M) (Q := P ∣ N) s2_2_4)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P ∣ M) (Q := P ∣ N) s2_2_4) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P ∣ M) (Q := P ∣ N) s2_2_4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P ∣ M) (Q := P ∣ N) s2_2_4); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 2.3. cases, from D2
      have s2_3 : P ∣ M * N := by
        rcases hD2 with hC3 | hC4
        · skip
          -- 2.3.1. mun:divides-multiple e := P, a := M, x := N, from C3
          have s2_3_1 : P ∣ M * N := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := M) (x := N) hC3) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := M) (x := N) hC3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := M) (x := N) hC3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := M) (x := N) hC3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := M) (x := N) hC3); parley_side)
          all_goals parley_side
        · skip
          -- 2.3.2. mun:divides-multiple e := P, a := N, x := M, from C4
          have s2_3_2 : P ∣ N * M := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := N) (x := M) hC4) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := N) (x := M) hC4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := N) (x := M) hC4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := N) (x := M) hC4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := P) (a := N) (x := M) hC4); parley_side)
          -- 2.3.3. substitute N·M = M·N (line 1) into line 2.3.2
          have s2_3_3 : P ∣ M * N := by parley_subst_at s1 s2_3_2
          all_goals parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.PrimeDividesProduct.PrimeDividesProduct
