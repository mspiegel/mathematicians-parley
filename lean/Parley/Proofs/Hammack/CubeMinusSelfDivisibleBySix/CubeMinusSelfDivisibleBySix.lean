module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive

/-! Written from proofs/hammack/cube-minus-self-divisible-by-six.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.CubeMinusSelfDivisibleBySix

theorem cube_minus_self_divisible_by_six (n : ℕ) :
    (6 : ℤ) ∣ (n : ℤ) ^ 3 - (n : ℤ) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (6 : ℤ) ∣ (k : ℤ) ^ 3 - (k : ℤ) := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (6 : ℤ) ∣ (0 ^ 3 : ℤ) := by parley_arith
      all_goals parley_side
    | succ k hIH =>
      -- 1.2. thm:six-divides-three-consecutive
      have s1_2 : (6 : ℤ) ∣ 3 * (k : ℤ) * ((k : ℤ) + 1) := by first | exact (Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k)) | exact ((Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k))).symm | simpa using (Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k)) | exact_mod_cast (Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k)) | (have h := (Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive.six_divides_three_consecutive (k := k)); parley_side)
      -- 1.3. mun:divides-sum d := 6, a := k³ − k, b := 3·k·(k + 1), from IH, 1.2
      have s1_3 : (6 : ℤ) ∣ (k : ℤ) ^ 3 - (k : ℤ) + 3 * (k : ℤ) * ((k : ℤ) + 1) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := (k : ℤ) ^ 3 - (k : ℤ)) (b := 3 * (k : ℤ) * ((k : ℤ) + 1)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := (k : ℤ) ^ 3 - (k : ℤ)) (b := 3 * (k : ℤ) * ((k : ℤ) + 1)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := (k : ℤ) ^ 3 - (k : ℤ)) (b := 3 * (k : ℤ) * ((k : ℤ) + 1)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := (k : ℤ) ^ 3 - (k : ℤ)) (b := 3 * (k : ℤ) * ((k : ℤ) + 1)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := (k : ℤ) ^ 3 - (k : ℤ)) (b := 3 * (k : ℤ) * ((k : ℤ) + 1)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (6 : ℤ)) (a := (k : ℤ) ^ 3 - (k : ℤ)) (b := 3 * (k : ℤ) * ((k : ℤ) + 1)) (by parley_side) (by parley_side)); parley_side)
      -- 1.4. substitute
      have s1_4 : (6 : ℤ) ∣ ((k : ℤ) + 1) ^ 3 - ((k : ℤ) + 1) := by
        have c1 : (k : ℤ) ^ 3 - (k : ℤ) + 3 * (k : ℤ) * ((k : ℤ) + 1) = ((k : ℤ) + 1) ^ 3 - ((k : ℤ) + 1) := by parley_ring
        have row1 : (6 : ℤ) ∣ ((k : ℤ) + 1) ^ 3 - ((k : ℤ) + 1) := by parley_subst_at c1 s1_3
        exact row1
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (6 : ℤ) ∣ (n : ℤ) ^ 3 - (n : ℤ) := by first | exact (s1 n) | exact ((s1 n)).symm | simpa using (s1 n) | exact_mod_cast (s1 n) | (have h := (s1 n); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (s1 n); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.CubeMinusSelfDivisibleBySix
