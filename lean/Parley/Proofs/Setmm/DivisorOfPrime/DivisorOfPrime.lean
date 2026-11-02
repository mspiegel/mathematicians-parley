module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/divisor-of-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DivisorOfPrime.DivisorOfPrime

theorem divisor_of_prime (P : ℕ) (hH1 : 0 < P) (hH2 : Nat.Prime P) (M : ℕ) (hH3 : 0 < M) :
    ((M : ℤ) ∣ (P : ℤ) ↔ (M : ℤ) = (P : ℤ) ∨ (M : ℤ) = 1) := by
  -- 1. def:prime p := P, from H2
  have s1 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (P : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (P : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. instantiate d := M in line 1
  have s2 : (M : ℤ) ∣ (P : ℤ) → (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ) := by first | exact (s1 M (by parley_side)) | exact ((s1 M (by parley_side))).symm | simpa using (s1 M (by parley_side)) | exact_mod_cast (s1 M (by parley_side)) | (have h := (s1 M (by parley_side)); parley_side)
  -- 3. both directions
  have s3 : (M : ℤ) ∣ (P : ℤ) ↔ (M : ℤ) = (P : ℤ) ∨ (M : ℤ) = 1 := by
    constructor
    · skip
      intro hD1
      -- 3.1. mun:modus-ponens, from D1, 2
      have s3_1 : (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (M : ℤ) ∣ (P : ℤ)) (Q := (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (M : ℤ) ∣ (P : ℤ)) (Q := (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (M : ℤ) ∣ (P : ℤ)) (Q := (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (M : ℤ) ∣ (P : ℤ)) (Q := (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (M : ℤ) ∣ (P : ℤ)) (Q := (M : ℤ) = 1 ∨ (M : ℤ) = (P : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 3.2. cases, from 3.1
      have s3_2 : (M : ℤ) = (P : ℤ) ∨ (M : ℤ) = 1 := by
        rcases s3_1 with hC1 | hC2
        · skip
          -- 3.2.1. mun:or-right P := M = P, Q := M = 1, from C1
          have s3_2_1 : (M : ℤ) = (P : ℤ) ∨ (M : ℤ) = 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)); parley_side)
          all_goals parley_side
        · skip
          -- 3.2.2. mun:or-left P := M = P, Q := M = 1, from C2
          have s3_2_2 : (M : ℤ) = (P : ℤ) ∨ (M : ℤ) = 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (M : ℤ) = (P : ℤ)) (Q := (M : ℤ) = 1) (by parley_side)); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 3.3. cases, from D2
      have s3_3 : (M : ℤ) ∣ (P : ℤ) := by
        rcases hD2 with hC3 | hC4
        · skip
          -- 3.3.1. mun:divides-self n := P
          have s3_3_1 : (P : ℤ) ∣ (P : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (P : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (P : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (P : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (P : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (P : ℤ))); parley_side)
          -- 3.3.2. substitute M = P (C3) into line 3.3.1
          have s3_3_2 : (M : ℤ) ∣ (P : ℤ) := by parley_subst_at hC3 s3_3_1
          all_goals parley_side
        · skip
          -- 3.3.3. def:divides d := 1, n := P
          have s3_3_3 : (1 : ℤ) ∣ (P : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (1 : ℤ)) (n := (P : ℤ)))).mpr ⟨(P : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (1 : ℤ)) (n := (P : ℤ)))).mpr ⟨(P : ℤ), by parley_side⟩; parley_side)
          -- 3.3.4. substitute M = 1 (C4) into line 3.3.3
          have s3_3_4 : (M : ℤ) ∣ (P : ℤ) := by parley_subst_at hC4 s3_3_3
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.DivisorOfPrime.DivisorOfPrime
