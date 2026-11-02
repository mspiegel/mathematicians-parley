module

public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd
public import Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient

theorem power_multiple_quotient (d : ℕ) (hH1 : 0 < d) (m : ℕ) (hH2 : 0 < m) :
    (∃ q : ℕ, 0 < q ∧ (2 ^ (d * m) - 1 = (2 ^ d - 1) * (q : ℤ) ∧ (q : ℤ) ≥ (m : ℤ))) := by
  -- 1. induction on j starting at 1
  have s1 : ∀ j : ℕ, 0 < j → (∃ q : ℕ, 0 < q ∧ (2 ^ (d * j) - 1 = (2 ^ d - 1) * (q : ℤ) ∧ (q : ℤ) ≥ (j : ℤ))) := by
    intro j h_j
    replace h_j : 1 ≤ j := h_j
    induction j, h_j using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) ≥ 1 := by parley_arith
      -- 1.2. exhibit, from 1.1
      have s1_2 : ∃ q : ℕ, 0 < q ∧ (2 ^ (d * 1) - 1 = (2 ^ d - 1) * (q : ℤ) ∧ (q : ℤ) ≥ 1) := ⟨1, by parley_side, by parley_side⟩
      all_goals parley_side
    | succ j hK hIH =>
      -- 1.3. obtain q from IH
      obtain ⟨q, s1_3a, s1_3b, s1_3c⟩ := hIH
      -- 1.4. algebra
      have s1_4 : (d : ℤ) * ((j : ℤ) + 1) = (d : ℤ) * (j : ℤ) + (d : ℤ) := by parley_ring
      -- 1.5. calculation
      have s1_5 : (2 ^ (d * (j + 1)) : ℤ) = 2 ^ (d * j) * 2 ^ d := by
        calc (2 ^ (d * (j + 1)) : ℤ) = 2 ^ (d * j + d) := by parley_subst s1_4
          _ = 2 ^ (d * j) * 2 ^ d := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)) | exact_mod_cast ((Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d))).symm | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerAdd.two_power_add (a := d * j) (b := d)); parley_side)
      -- 1.6. calculation
      have s1_6 : 2 ^ (d * (j + 1)) - 1 = (2 ^ d - 1) * (2 ^ d * (q : ℤ) + 1) := by
        calc (2 ^ (d * (j + 1)) - 1 : ℤ) = 2 ^ (d * j) * 2 ^ d - 1 := by parley_subst s1_5
          _ = 2 ^ d * (2 ^ (d * j) - 1) + (2 ^ d - 1) := by parley_ring
          _ = 2 ^ d * ((2 ^ d - 1) * (q : ℤ)) + (2 ^ d - 1) := by parley_subst s1_3b
          _ = (2 ^ d - 1) * (2 ^ d * (q : ℤ) + 1) := by parley_ring
      -- 1.7. thm:two-power-bound
      have s1_7 : 2 ^ d ≥ (d : ℤ) + 1 := by first | linarith [(Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side))] | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side)) | (have h := (Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound.two_power_bound (d := d) (by parley_side)); parley_side)
      -- 1.8. inequalities, from H1
      have s1_8 : (d : ℤ) + 1 ≥ 1 := by parley_side
      -- 1.9. transitivity, from 1.7, 1.8
      have s1_9 : (2 ^ d : ℤ) ≥ 1 := by parley_side
      -- 1.10. mun:multiply-le x := 1, y := 2^d, c := q, from 1.9
      have r134_1 : (q : ℤ) > 0 := by parley_side
      have s1_10 : (q : ℤ) * 1 ≤ (q : ℤ) * 2 ^ d := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (2 ^ d : ℤ)) (c := (q : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (2 ^ d : ℤ)) (c := (q : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (2 ^ d : ℤ)) (c := (q : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (2 ^ d : ℤ)) (c := (q : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 1.11. algebra
      have s1_11 : (q : ℤ) * 2 ^ d = 2 ^ d * (q : ℤ) := by parley_ring
      -- 1.12. inequalities
      have s1_12 : (q : ℤ) ≤ (q : ℤ) * 2 ^ d := by parley_side
      -- 1.13. inequalities, from 1.3
      have s1_13 : (j : ℤ) ≤ (q : ℤ) := by parley_side
      -- 1.14. transitivity, from 1.13, 1.12, 1.11
      have s1_14 : (j : ℤ) ≤ 2 ^ d * (q : ℤ) := by parley_side
      -- 1.15. inequalities
      have s1_15 : 2 ^ d * (q : ℤ) + 1 ≥ (j : ℤ) + 1 := by parley_side
      -- 1.16. exhibit, from 1.6, 1.15
      have s1_16 : ∃ q : ℕ, 0 < q ∧ (2 ^ (d * (j + 1)) - 1 = (2 ^ d - 1) * (q : ℤ) ∧ (q : ℤ) ≥ (j : ℤ) + 1) := ⟨2 ^ d * q + 1, by parley_side, by parley_side⟩
      all_goals parley_side
  -- 2. instantiate j := m in line 1
  have s2 : ∃ q : ℕ, 0 < q ∧ (2 ^ (d * m) - 1 = (2 ^ d - 1) * (q : ℤ) ∧ (q : ℤ) ≥ (m : ℤ)) := by first | exact (s1 m (by parley_side)) | exact ((s1 m (by parley_side))).symm | simpa using (s1 m (by parley_side)) | exact_mod_cast (s1 m (by parley_side)) | (have h := (s1 m (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (s1 m (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.MersennePrimeExponent.PowerMultipleQuotient
