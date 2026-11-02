module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/prime-sum-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeSumOdd.PrimeSumOdd

theorem prime_sum_odd (p : ℕ) (hH1 : 0 < p) (q : ℕ) (hH2 : 0 < q) (hH3 : Nat.Prime p) (hH4 : Nat.Prime q) (hH5 : (p : ℤ) < (q : ℤ)) :
    Odd (2 * (p : ℤ) + (q : ℤ) ^ 2) := by
  -- 1. def:prime, from H3
  have s1 : (p : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. mun:integer-step m := 1, n := p, from 1
  have s2 : 1 + 1 ≤ (p : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (p : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (p : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (p : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (p : ℤ)) (by parley_side)); parley_side)
  -- 3. transitivity, from 2, H5
  have s3 : 1 + 1 < (q : ℤ) := by parley_side
  -- 4. def:prime p := q, from H4
  have s4 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (q : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (q : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := q) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := q) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_prime (p := q) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := q) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := q) (by parley_side))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := q) (by parley_side))).mp (by parley_side); parley_side)
  -- 5. mun:even-or-odd n := q
  have s5 : Even (q : ℤ) ∨ Odd (q : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (q : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (q : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (q : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (q : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (q : ℤ))); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (q : ℤ))); parley_side)
  -- 6. cases, from 5
  have s6 : Odd (q : ℤ) := by
    rcases s5 with hC1 | hC4
    · skip
      -- 6.1. obtain k: def:even n := q, from C1
      obtain ⟨k, s6_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (q : ℤ)))).mp (by parley_side)
      -- 6.2. def:divides d := 2, n := q, from 6.1
      have s6_2 : (2 : ℤ) ∣ (q : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (q : ℤ)))).mpr ⟨k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (q : ℤ)))).mpr ⟨k, by parley_side⟩; parley_side)
      -- 6.3. instantiate d := 2 in line 4
      have s6_3 : (2 : ℤ) ∣ (q : ℤ) → (2 : ℤ) = 1 ∨ 2 = (q : ℤ) := by first | exact (s4 2 (by parley_side)) | exact ((s4 2 (by parley_side))).symm | simpa using (s4 2 (by parley_side)) | exact_mod_cast (s4 2 (by parley_side)) | (have h := (s4 2 (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (s4 2 (by parley_side)); parley_side)
      -- 6.4. mun:modus-ponens P := 2 divides q, from 6.2, 6.3
      have s6_4 : (2 : ℤ) = 1 ∨ 2 = (q : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (q : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (q : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (q : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (q : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (q : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (q : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (q : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (q : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (q : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (q : ℤ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ (q : ℤ)) (Q := (2 : ℤ) = 1 ∨ 2 = (q : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 6.5. cases, from 6.4
      have s6_5 : 2 = (q : ℤ) := by
        rcases s6_4 with hC2 | hC3
        · skip
          -- 6.5.1. arithmetic
          have s6_5_1 : (2 : ℤ) ≠ 1 := by parley_arith
          all_goals parley_side
        · skip
          all_goals parley_side
      -- 6.6. inequalities
      have s6_6 : 2 ≠ (q : ℤ) := by parley_side
      all_goals parley_side
    · skip
      all_goals parley_side
  -- 7. obtain k: def:odd n := q, from 6
  obtain ⟨k, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (q : ℤ)))).mp (by parley_side)
  -- 8. algebra, from 7
  have s8 : 2 * (p : ℤ) + (q : ℤ) ^ 2 = 2 * ((p : ℤ) + 2 * k ^ 2 + 2 * k) + 1 := by linear_combination (norm := parley_norm) (2 * k + (q : ℤ) + 1) * s7
  -- 9. def:odd n := 2p + q², from 8
  have s9 : Odd (2 * (p : ℤ) + (q : ℤ) ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := 2 * (p : ℤ) + (q : ℤ) ^ 2))).mpr ⟨(p : ℤ) + 2 * k ^ 2 + 2 * k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 2 * (p : ℤ) + (q : ℤ) ^ 2))).mpr ⟨(p : ℤ) + 2 * k ^ 2 + 2 * k, by parley_side⟩; parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.PrimeSumOdd.PrimeSumOdd
