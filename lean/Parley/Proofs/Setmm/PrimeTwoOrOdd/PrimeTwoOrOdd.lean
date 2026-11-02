module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-two-or-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeTwoOrOdd.PrimeTwoOrOdd

theorem prime_two_or_odd (P : ℕ) (hH1 : 0 < P) (hH2 : Nat.Prime P) :
    ((P : ℤ) = 2 ∨ Odd (P : ℤ)) := by
  -- 1. mun:even-or-odd n := P
  have s1 : Even (P : ℤ) ∨ Odd (P : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (P : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (P : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (P : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (P : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (P : ℤ))); parley_side)
  -- 2. cases, from 1
  have s2 : (P : ℤ) = 2 ∨ Odd (P : ℤ) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even n := P, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (P : ℤ)))).mp (by parley_side)
      -- 2.2. def:divides d := 2, n := P, from 2.1
      have s2_2 : (2 : ℤ) ∣ (P : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (P : ℤ)))).mpr ⟨k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (P : ℤ)))).mpr ⟨k, by parley_side⟩; parley_side)
      -- 2.3. def:prime p := P, from H2
      have s2_3 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (P : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (P : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
      -- 2.4. instantiate d := 2 in line 2.3
      have s2_4 : (2 : ℤ) ∣ (P : ℤ) → (2 : ℤ) = 1 ∨ 2 = (P : ℤ) := by first | exact (s2_3 2 (by parley_side)) | exact ((s2_3 2 (by parley_side))).symm | simpa using (s2_3 2 (by parley_side)) | exact_mod_cast (s2_3 2 (by parley_side)) | (have h := (s2_3 2 (by parley_side)); parley_side)
      -- 2.5. mun:modus-ponens, from 2.2, 2.4
      have s2_5 : (2 : ℤ) = 1 ∨ 2 = (P : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (P : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (P : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (P : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (P : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (P : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (P : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (P : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (P : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (P : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (P : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 2.6. cases, from 2.5
      have s2_6 : 2 = (P : ℤ) := by
        rcases s2_5 with hC3 | hC4
        · skip
          -- 2.6.1. arithmetic
          have s2_6_1 : (2 : ℤ) ≠ 1 := by parley_arith
          all_goals parley_side
        · skip
          all_goals parley_side
      -- 2.7. restate 2.6
      have s2_7 : (P : ℤ) = 2 := by parley_side
      -- 2.8. mun:or-left P := P = 2, Q := P is odd, from 2.7
      have s2_8 : (P : ℤ) = 2 ∨ Odd (P : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      -- 2.9. mun:or-right P := P = 2, Q := P is odd, from C2
      have s2_9 : (P : ℤ) = 2 ∨ Odd (P : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (P : ℤ) = 2) (Q := Odd (P : ℤ)) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.PrimeTwoOrOdd.PrimeTwoOrOdd
