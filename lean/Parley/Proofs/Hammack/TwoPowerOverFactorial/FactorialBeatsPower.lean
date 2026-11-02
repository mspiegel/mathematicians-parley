module

public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/two-power-over-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

theorem factorial_beats_power (n : ℕ) (hH1 : 0 < n) :
    (n : ℤ) * 2 ^ n ≤ 4 * (Parley.Library.factorial (n : ℤ) : ℤ) := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → 2 ^ k ≤ 2 * (Parley.Library.factorial (k : ℤ) : ℤ) ∧ (k : ℤ) * 2 ^ k ≤ 4 * (Parley.Library.factorial (k : ℤ) : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : 2 ^ 1 ≤ 2 * (Parley.Library.factorial (1 : ℤ) : ℤ) := by parley_arith
      -- 1.2. arithmetic
      have s1_2 : 1 * 2 ^ 1 ≤ 4 * (Parley.Library.factorial (1 : ℤ) : ℤ) := by parley_arith
      -- 1.3. join 1.1, 1.2
      have s1_3 : 2 ^ 1 ≤ 2 * (Parley.Library.factorial (1 : ℤ) : ℤ) ∧ 1 * 2 ^ 1 ≤ 4 * (Parley.Library.factorial (1 : ℤ) : ℤ) := by parley_side
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.4. mun:factorial-nat n := k
      have s1_4 : 0 < (Parley.Library.factorial (k : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k))
      -- 1.5. inequalities, from 1.4
      have s1_5 : (Parley.Library.factorial (k : ℤ) : ℤ) > 0 := by parley_side
      -- 1.6. def:factorial n := k
      have s1_6 : (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) = (Parley.Library.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := k))).symm
      -- 1.7. mun:exponent-step a := 2, m := k
      have s1_7 : (2 ^ (k + 1) : ℤ) = 2 ^ k * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k))).symm
      -- 1.8. inequalities
      have s1_8 : 2 ^ k * 2 ≤ 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * 2 := by parley_side
      -- 1.9. inequalities, from K
      have s1_9 : (k : ℤ) ≥ 1 := by parley_side
      -- 1.10. inequalities
      have s1_10 : (k : ℤ) + 1 ≥ 2 := by parley_side
      -- 1.11. inequalities
      have s1_11 : 2 * (Parley.Library.factorial (k : ℤ) : ℤ) > 0 := by parley_side
      -- 1.12. mun:multiply-le x := 2, y := k + 1, c := 2·k!, from 1.10, 1.11
      have s1_12 : 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * 2 ≤ 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (k : ℤ) + 1) (c := 2 * (Parley.Library.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (k : ℤ) + 1) (c := 2 * (Parley.Library.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 : ℤ)) (y := (k : ℤ) + 1) (c := 2 * (Parley.Library.factorial (k : ℤ) : ℤ)) (by parley_side) (by parley_side))
      -- 1.13. algebra, from 1.6
      have s1_13 : 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) = 2 * (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) := by linear_combination (norm := parley_norm) (-2) * s1_6
      -- 1.14. transitivity, from 1.7, 1.8, 1.12, 1.13
      have s1_14 : 2 ^ (k + 1) ≤ 2 * (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) := by parley_side
      -- 1.15. calculation
      have r78_1 : (k : ℤ) + 1 > 0 := by parley_side
      have s1_15 : ((k : ℤ) + 1) * 2 ^ (k + 1) ≤ 4 * (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) := by
        calc ((k : ℤ) + 1) * 2 ^ (k + 1) = ((k : ℤ) + 1) * (2 ^ k * 2) := by linear_combination (norm := parley_norm) ((k : ℤ) + 1) * s1_7
          _ ≤ ((k : ℤ) + 1) * (2 * (Parley.Library.factorial (k : ℤ) : ℤ) * 2) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k * 2 : ℤ)) (y := 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * 2) (c := (k : ℤ) + 1) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k * 2 : ℤ)) (y := 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * 2) (c := (k : ℤ) + 1) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (2 ^ k * 2 : ℤ)) (y := 2 * (Parley.Library.factorial (k : ℤ) : ℤ) * 2) (c := (k : ℤ) + 1) (by parley_side) (by parley_side))
          _ = 4 * (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) := by linear_combination (norm := parley_norm) (-4) * s1_6
      -- 1.16. join 1.14, 1.15
      have s1_16 : 2 ^ (k + 1) ≤ 2 * (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) ∧ ((k : ℤ) + 1) * 2 ^ (k + 1) ≤ 4 * (Parley.Library.factorial ((k : ℤ) + 1) : ℤ) := by parley_side
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : 2 ^ n ≤ 2 * (Parley.Library.factorial (n : ℤ) : ℤ) ∧ (n : ℤ) * 2 ^ n ≤ 4 * (Parley.Library.factorial (n : ℤ) : ℤ) := by first | exact (s1 n (by parley_side)) | exact ((s1 n (by parley_side))).symm | simpa using (s1 n (by parley_side)) | exact_mod_cast (s1 n (by parley_side))
  -- 3. restate 2
  have s3 : (n : ℤ) * 2 ^ n ≤ 4 * (Parley.Library.factorial (n : ℤ) : ℤ) := by parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower
