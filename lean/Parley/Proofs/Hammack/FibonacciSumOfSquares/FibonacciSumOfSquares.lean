module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence

/-! Written from proofs/hammack/fibonacci-sum-of-squares.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciSumOfSquares.FibonacciSumOfSquares

set_option maxHeartbeats 600000 in
theorem fibonacci_sum_of_squares (n : ℕ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (F k ^ 2 : ℤ)) = F (n : ℤ) * F ((n : ℤ) + 1) := by
  -- 1. thm:fibonacci-natural
  have s1 : ∀ k : ℕ, 0 ≤ F (k : ℤ) ∧ 0 ≤ G (k : ℤ) := by first | exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | exact ((Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | (have h := (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)); parley_side)
  -- 2. proof
  -- what this block shows, Lean's types give
  set q : ℤ → ℤ := fun j => F j ^ 2 with hD2
  -- 3. thm:fibonacci-recurrence
  have s3 : ∀ k : ℕ, F ((k : ℤ) + 2) = F (k : ℤ) + F ((k : ℤ) + 1) := by first | exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)) | exact ((Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)) | (have h := (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)); parley_side)
  -- 4. induction on m starting at 1
  have s4 : ∀ m : ℕ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (q j : ℤ)) = F (m : ℤ) * F ((m : ℤ) + 1) := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 4.1. proof
      -- what this block shows, Lean's types give
      -- 4.2. mun:sum-single a := 1
      have s4_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (q j : ℤ)) = q 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := q) (a := (1 : ℤ))); parley_side)
      -- 4.3. D1
      have s4_3 : F 1 = G 0 := by have h := (hD1.2.2 ((1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.4. D1
      have s4_4 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.5. D1
      have s4_5 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.6. calculation
      have s4_6 : F 1 = 1 := by
        calc F 1 = G 0 := by parley_side
          _ = 1 := by parley_side
      -- 4.7. instantiate k := 0 in line 3
      have s4_7 : F 2 = F 0 + F 1 := by first | linear_combination (norm := parley_norm) (s3 0) | (have h := (s3 0); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s3 0); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s3 0) | exact_mod_cast ((s3 0)).symm | (have h := (s3 0); rify; linear_combination (norm := parley_norm) h) | (have h := (s3 0); qify; linear_combination (norm := parley_norm) h) | (have h := (s3 0); parley_int_power h) | (have h := (s3 0); parley_side)
      -- 4.8. calculation
      have s4_8 : F (1 + 1) = 1 := by
        calc F (1 + 1) = F 2 := by norm_num
          _ = 1 := by linear_combination (norm := parley_norm) s4_5 + s4_6 + s4_7
      -- 4.9. algebra, from D2, 4.2, 4.6, 4.8
      have s4_9 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (q j : ℤ)) = F 1 * F (1 + 1) := by
        try simp only [hD2] at *
        try push_cast at *
        linear_combination (norm := parley_norm) s4_2 + (-F (1 + 1) + F 1 + 1) * s4_6 + (-1) * s4_8
      all_goals parley_side
    | succ m hK3 hIH2 =>
      -- 4.10. proof
      -- what this block shows, Lean's types give
      -- 4.11. mun:sum-extended a := 1, n := m
      have r90_1 : (m : ℤ) ≥ 1 := by parley_side
      have s4_11 : (∑ j ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (q j : ℤ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (q j : ℤ)) + q ((m : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := q) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_side)
      -- 4.12. instantiate k := m in line 3
      have s4_12 : F ((m : ℤ) + 2) = F (m : ℤ) + F ((m : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (s3 m) | (have h := (s3 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s3 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s3 m) | exact_mod_cast ((s3 m)).symm | (have h := (s3 m); rify; linear_combination (norm := parley_norm) h) | (have h := (s3 m); qify; linear_combination (norm := parley_norm) h) | (have h := (s3 m); parley_int_power h) | (have h := (s3 m); parley_side)
      -- 4.13. instantiate k := m in line 2
      -- 4.14. instantiate k := m + 1 in line 2
      -- 4.15. algebra, from D2, IH2, 4.11, 4.12
      have s4_15 : (∑ j ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (q j : ℤ)) = F ((m : ℤ) + 1) * F ((m : ℤ) + 2) := by
        try simp only [hD2] at *
        try push_cast at *
        linear_combination (norm := parley_norm) hIH2 + s4_11 + (-F ((m : ℤ) + 1)) * s4_12
      -- 4.16. substitute
      have s4_16 : (∑ j ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (q j : ℤ)) = F ((m : ℤ) + 1) * F ((m : ℤ) + 1 + 1) := by
        have c1 : (m : ℤ) + 2 = (m : ℤ) + 1 + 1 := by parley_ring
        have row1 : (∑ j ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (q j : ℤ)) = F ((m : ℤ) + 1) * F ((m : ℤ) + 1 + 1) := by parley_subst_at c1 s4_15
        exact row1
      all_goals parley_side
  -- 5. instantiate m := n in line 4, from D2
  have s5 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (F k ^ 2 : ℤ)) = F (n : ℤ) * F ((n : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (s4 n (by parley_side)) | (have h := (s4 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s4 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s4 n (by parley_side)) | exact_mod_cast ((s4 n (by parley_side))).symm | (have h := (s4 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s4 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s4 n (by parley_side)); parley_int_power h) | (have h := (s4 n (by parley_side)); parley_side)
  all_goals exact s5

end Parley.Proofs.Hammack.FibonacciSumOfSquares.FibonacciSumOfSquares
