module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/divisor-of-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DivisorOfPrime.DivisorOfPrime

set_option maxHeartbeats 400000 in
theorem divisor_of_prime (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (M : ℤ) (hH3 : 0 < M) :
    (M ∣ P ↔ M = P ∨ M = 1) := by
  -- 1. def:prime p := P, from H2
  have s1 : ∀ d : ℤ, 0 < d → d ∣ P → d = 1 ∨ d = P := by first | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).2; parley_side)
  -- 2. instantiate d := M in line 1
  have s2 : M ∣ P → M = 1 ∨ M = P := by first | exact (s1 M (by parley_side)) | exact ((s1 M (by parley_side))).symm | simpa using (s1 M (by parley_side)) | exact_mod_cast (s1 M (by parley_side)) | (have h := (s1 M (by parley_side)); parley_side)
  -- 3. both directions
  have s3 : M ∣ P ↔ M = P ∨ M = 1 := by
    constructor
    · skip
      intro hD1
      -- 3.1. mun:modus-ponens, from D1, 2
      have s3_1 : M = 1 ∨ M = P := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := M ∣ P) (Q := M = 1 ∨ M = P) s2 hD1) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := M ∣ P) (Q := M = 1 ∨ M = P) s2 hD1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := M ∣ P) (Q := M = 1 ∨ M = P) s2 hD1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := M ∣ P) (Q := M = 1 ∨ M = P) s2 hD1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := M ∣ P) (Q := M = 1 ∨ M = P) s2 hD1); parley_side)
      -- 3.2. cases, from 3.1
      have s3_2 : M = P ∨ M = 1 := by
        rcases s3_1 with hC1 | hC2
        · skip
          -- 3.2.1. mun:or-right P := M = P, Q := M = 1, from C1
          have s3_2_1 : M = P ∨ M = 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := M = P) (Q := M = 1) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := M = P) (Q := M = 1) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := M = P) (Q := M = 1) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := M = P) (Q := M = 1) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := M = P) (Q := M = 1) hC1); parley_side)
          all_goals parley_side
        · skip
          -- 3.2.2. mun:or-left P := M = P, Q := M = 1, from C2
          have s3_2_2 : M = P ∨ M = 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := M = P) (Q := M = 1) hC2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := M = P) (Q := M = 1) hC2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := M = P) (Q := M = 1) hC2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := M = P) (Q := M = 1) hC2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := M = P) (Q := M = 1) hC2); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 3.3. cases, from D2
      have s3_3 : M ∣ P := by
        rcases hD2 with hC3 | hC4
        · skip
          -- 3.3.1. mun:divides-self n := P
          have s3_3_1 : P ∣ P := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := P)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := P))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := P)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := P)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := P)); parley_side)
          -- 3.3.2. substitute M = P (C3) into line 3.3.1
          have s3_3_2 : M ∣ P := by parley_subst_at hC3 s3_3_1
          all_goals parley_side
        · skip
          -- 3.3.3. def:divides d := 1, n := P
          have s3_3_3 : (1 : ℤ) ∣ P := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (1 : ℤ)) (n := P))).mpr ⟨P, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (1 : ℤ)) (n := P))).mpr ⟨P, by parley_side⟩; parley_side)
          -- 3.3.4. substitute M = 1 (C4) into line 3.3.3
          have s3_3_4 : M ∣ P := by parley_subst_at hC4 s3_3_3
          all_goals parley_side
      all_goals parley_side
  all_goals exact s3

end Parley.Proofs.Setmm.DivisorOfPrime.DivisorOfPrime
