module

public import AlgebraTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree
public import Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence
public import Parley.Proofs.Setmm.Parity.EvenPlusOdd
public import Parley.Proofs.Setmm.Parity.OddPlusOdd

/-! Written from proofs/hammack/fibonacci-even-iff-three-divides.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.FibonacciEvenIffThreeDivides

set_option maxHeartbeats 1600000 in
theorem fibonacci_even_iff_three_divides (n : ℤ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (Even (F n) ↔ (3 : ℤ) ∣ n) := by
  -- 1. thm:fibonacci-natural
  have s1 : ∀ k : ℤ, 0 ≤ k → 0 ≤ F k ∧ 0 ≤ G k := by first | exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | exact ((Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | (have h := (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)); parley_side)
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. thm:fibonacci-recurrence
  have s3 : ∀ k : ℤ, 0 ≤ k → F (k + 2) = F k + F (k + 1) := by first | exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)) | exact ((Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)) | (have h := (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciRecurrence.fibonacci_recurrence (F := F) (G := G) (by parley_side)); parley_side)
  -- 4. induction on k starting at 0
  have s4 : ∀ k : ℤ, 0 ≤ k → (Even (F (3 * k)) ∧ Odd (F (3 * k + 1))) ∧ Odd (F (3 * k + 2)) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 4.1. D1
      have s4_1 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.2. D1
      have s4_2 : F 1 = G 0 := by have h := (hD1.2.2 ((1 : ℤ) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.3. D1
      have s4_3 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.4. calculation
      have s4_4 : F 1 = 1 := by
        calc F 1 = G 0 := by parley_side
          _ = 1 := by parley_side
      -- 4.5. instantiate k := 0 in line 3
      have s4_5 : F 2 = F 0 + F 1 := by first | linear_combination (norm := parley_norm) (s3 (0 : ℤ) (by parley_side)) | (have h := (s3 (0 : ℤ) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s3 (0 : ℤ) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s3 (0 : ℤ) (by parley_side)) | exact_mod_cast ((s3 (0 : ℤ) (by parley_side))).symm | (have h := (s3 (0 : ℤ) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s3 (0 : ℤ) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s3 (0 : ℤ) (by parley_side)); parley_int_power h) | (have h := (s3 (0 : ℤ) (by parley_side)); parley_side)
      -- 4.6. calculation
      have s4_6 : F (3 * 0) = 2 * 0 := by
        calc F (3 * 0) = F 0 := by norm_num
          _ = 0 := by parley_side
          _ = 2 * 0 := by norm_num
      -- 4.7. def:even n := F(3·0), from 4.6
      have s4_7 : Even (F (3 * 0)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := F (3 * 0)))).mpr ⟨(0 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := F (3 * 0)))).mpr ⟨(0 : ℤ), by parley_side⟩; parley_side)
      -- 4.8. calculation
      have s4_8 : F (3 * 0 + 1) = 2 * 0 + 1 := by
        calc F (3 * 0 + 1) = F 1 := by norm_num
          _ = 1 := by parley_side
          _ = 2 * 0 + 1 := by norm_num
      -- 4.9. def:odd n := F(3·0 + 1), from 4.8
      have s4_9 : Odd (F (3 * 0 + 1)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := F (3 * 0 + 1)))).mpr ⟨(0 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := F (3 * 0 + 1)))).mpr ⟨(0 : ℤ), by parley_side⟩; parley_side)
      -- 4.10. calculation
      have s4_10 : F (3 * 0 + 2) = 2 * 0 + 1 := by
        calc F (3 * 0 + 2) = F 2 := by norm_num
          _ = 1 := by linear_combination (norm := parley_norm) s4_1 + s4_4 + s4_5
          _ = 2 * 0 + 1 := by norm_num
      -- 4.11. def:odd n := F(3·0 + 2), from 4.10
      have s4_11 : Odd (F (3 * 0 + 2)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := F (3 * 0 + 2)))).mpr ⟨(0 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := F (3 * 0 + 2)))).mpr ⟨(0 : ℤ), by parley_side⟩; parley_side)
      -- 4.12. join 4.7, 4.9, 4.11
      have s4_12 : (Even (F (3 * 0)) ∧ Odd (F (3 * 0 + 1))) ∧ Odd (F (3 * 0 + 2)) := by parley_side
      all_goals parley_side
    | succ k hK3 hIH2 =>
      -- 4.13. instantiate k := 3k + 1 in line 2
      -- 4.14. instantiate k := 3k + 2 in line 2
      -- 4.15. instantiate k := 3k + 1 in line 3
      have s4_15 : F (3 * k + 1 + 2) = F (3 * k + 1) + F (3 * k + 1 + 1) := by first | linear_combination (norm := parley_norm) (s3 (3 * k + 1) (by parley_side)) | (have h := (s3 (3 * k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s3 (3 * k + 1) (by parley_side)) | exact_mod_cast ((s3 (3 * k + 1) (by parley_side))).symm | (have h := (s3 (3 * k + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * k + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * k + 1) (by parley_side)); parley_int_power h) | (have h := (s3 (3 * k + 1) (by parley_side)); parley_side)
      -- 4.16. substitute
      have s4_16 : F (3 * (k + 1)) = F (3 * k + 1) + F (3 * k + 1 + 1) := by
        have c1 : 3 * k + 1 + 2 = 3 * (k + 1) := by parley_ring
        have row1 : F (3 * (k + 1)) = F (3 * k + 1) + F (3 * k + 1 + 1) := by parley_subst_at c1 s4_15
        exact row1
      -- 4.17. substitute
      have s4_17 : F (3 * (k + 1)) = F (3 * k + 1) + F (3 * k + 2) := by
        have c1 : 3 * k + 1 + 1 = 3 * k + 2 := by parley_ring
        have row1 : F (3 * (k + 1)) = F (3 * k + 1) + F (3 * k + 2) := by parley_subst_at c1 s4_16
        exact row1
      -- 4.18. thm:odd-plus-odd A := F(3k + 1), B := F(3k + 2), from IH2
      have s4_18 : Even (F (3 * k + 1) + F (3 * k + 2)) := by first | exact (Parley.Proofs.Setmm.Parity.OddPlusOdd.odd_plus_odd (A := F (3 * k + 1)) (B := F (3 * k + 2)) hIH2.1.2 hIH2.2) | exact ((Parley.Proofs.Setmm.Parity.OddPlusOdd.odd_plus_odd (A := F (3 * k + 1)) (B := F (3 * k + 2)) hIH2.1.2 hIH2.2)).symm | simpa using (Parley.Proofs.Setmm.Parity.OddPlusOdd.odd_plus_odd (A := F (3 * k + 1)) (B := F (3 * k + 2)) hIH2.1.2 hIH2.2) | exact_mod_cast (Parley.Proofs.Setmm.Parity.OddPlusOdd.odd_plus_odd (A := F (3 * k + 1)) (B := F (3 * k + 2)) hIH2.1.2 hIH2.2) | (have h := (Parley.Proofs.Setmm.Parity.OddPlusOdd.odd_plus_odd (A := F (3 * k + 1)) (B := F (3 * k + 2)) hIH2.1.2 hIH2.2); parley_side)
      -- 4.19. substitute F(3(k + 1)) = F(3k + 1) + F(3k + 2) (line 4.17) into line 4.18
      have s4_19 : Even (F (3 * (k + 1))) := by parley_subst_at s4_17 s4_18
      -- 4.20. instantiate k := 3k + 2 in line 3
      have s4_20 : F (3 * k + 2 + 2) = F (3 * k + 2) + F (3 * k + 2 + 1) := by first | linear_combination (norm := parley_norm) (s3 (3 * k + 2) (by parley_side)) | (have h := (s3 (3 * k + 2) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * k + 2) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s3 (3 * k + 2) (by parley_side)) | exact_mod_cast ((s3 (3 * k + 2) (by parley_side))).symm | (have h := (s3 (3 * k + 2) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * k + 2) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * k + 2) (by parley_side)); parley_int_power h) | (have h := (s3 (3 * k + 2) (by parley_side)); parley_side)
      -- 4.21. substitute
      have s4_21 : F (3 * (k + 1) + 1) = F (3 * k + 2) + F (3 * k + 2 + 1) := by
        have c1 : 3 * k + 2 + 2 = 3 * (k + 1) + 1 := by parley_ring
        have row1 : F (3 * (k + 1) + 1) = F (3 * k + 2) + F (3 * k + 2 + 1) := by parley_subst_at c1 s4_20
        exact row1
      -- 4.22. substitute
      have s4_22 : F (3 * (k + 1) + 1) = F (3 * k + 2) + F (3 * (k + 1)) := by
        have c1 : 3 * k + 2 + 1 = 3 * (k + 1) := by parley_ring
        have row1 : F (3 * (k + 1) + 1) = F (3 * k + 2) + F (3 * (k + 1)) := by parley_subst_at c1 s4_21
        exact row1
      -- 4.23. instantiate k := 3(k + 1) in line 2
      -- 4.24. thm:odd-plus-even A := F(3k + 2), B := F(3(k + 1)), from IH2, 4.19
      have s4_24 : Odd (F (3 * k + 2) + F (3 * (k + 1))) := by first | exact (Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven.odd_plus_even (A := F (3 * k + 2)) (B := F (3 * (k + 1))) hIH2.2 s4_19) | exact ((Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven.odd_plus_even (A := F (3 * k + 2)) (B := F (3 * (k + 1))) hIH2.2 s4_19)).symm | simpa using (Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven.odd_plus_even (A := F (3 * k + 2)) (B := F (3 * (k + 1))) hIH2.2 s4_19) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven.odd_plus_even (A := F (3 * k + 2)) (B := F (3 * (k + 1))) hIH2.2 s4_19) | (have h := (Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven.odd_plus_even (A := F (3 * k + 2)) (B := F (3 * (k + 1))) hIH2.2 s4_19); parley_side)
      -- 4.25. substitute F(3(k + 1) + 1) = F(3k + 2) + F(3(k + 1)) (line 4.22) into line 4.24
      have s4_25 : Odd (F (3 * (k + 1) + 1)) := by parley_subst_at s4_22 s4_24
      -- 4.26. instantiate k := 3(k + 1) + 1 in line 2
      -- 4.27. thm:even-plus-odd A := F(3(k + 1)), B := F(3(k + 1) + 1), from 4.19, 4.25
      have s4_27 : Odd (F (3 * (k + 1)) + F (3 * (k + 1) + 1)) := by first | exact (Parley.Proofs.Setmm.Parity.EvenPlusOdd.even_plus_odd (A := F (3 * (k + 1))) (B := F (3 * (k + 1) + 1)) s4_19 s4_25) | exact ((Parley.Proofs.Setmm.Parity.EvenPlusOdd.even_plus_odd (A := F (3 * (k + 1))) (B := F (3 * (k + 1) + 1)) s4_19 s4_25)).symm | simpa using (Parley.Proofs.Setmm.Parity.EvenPlusOdd.even_plus_odd (A := F (3 * (k + 1))) (B := F (3 * (k + 1) + 1)) s4_19 s4_25) | exact_mod_cast (Parley.Proofs.Setmm.Parity.EvenPlusOdd.even_plus_odd (A := F (3 * (k + 1))) (B := F (3 * (k + 1) + 1)) s4_19 s4_25) | (have h := (Parley.Proofs.Setmm.Parity.EvenPlusOdd.even_plus_odd (A := F (3 * (k + 1))) (B := F (3 * (k + 1) + 1)) s4_19 s4_25); parley_side)
      -- 4.28. substitute
      have s4_28 : Odd (F (3 * (k + 1) + 2)) := by
        have c1 : F (3 * (k + 1)) + F (3 * (k + 1) + 1) = F (3 * (k + 1) + 2) := by first | linear_combination (norm := parley_norm) (s3 (3 * (k + 1)) (by parley_side)) | (have h := (s3 (3 * (k + 1)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * (k + 1)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s3 (3 * (k + 1)) (by parley_side)) | exact_mod_cast ((s3 (3 * (k + 1)) (by parley_side))).symm | (have h := (s3 (3 * (k + 1)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * (k + 1)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s3 (3 * (k + 1)) (by parley_side)); parley_int_power h) | (have h := (s3 (3 * (k + 1)) (by parley_side)); parley_side)
        have row1 : Odd (F (3 * (k + 1) + 2)) := by parley_subst_at c1 s4_27
        exact row1
      -- 4.29. join 4.19, 4.25, 4.28
      have s4_29 : (Even (F (3 * (k + 1))) ∧ Odd (F (3 * (k + 1) + 1))) ∧ Odd (F (3 * (k + 1) + 2)) := by parley_side
      all_goals parley_side
  -- 5. both directions
  have s5 : Even (F n) ↔ (3 : ℤ) ∣ n := by
    constructor
    · skip
      intro hP1
      -- 5.1. mun:mod-natural a := n, b := 3
      have s5_1 : 0 ≤ n % (3 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by parley_side)); parley_side)
      -- 5.2. mun:mod-less a := n, b := 3
      have s5_2 : n % (3 : ℤ) < 3 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by parley_side)); parley_side)
      -- 5.3. thm:residue-mod-three r := n mod 3, from 5.1, 5.2
      have s5_3 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by first | exact (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (by parley_side) s5_2) | exact ((Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (by parley_side) s5_2)).symm | simpa using (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (by parley_side) s5_2) | exact_mod_cast (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (by parley_side) s5_2) | (have h := (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (by parley_side) s5_2); parley_side)
      -- 5.4. obtain q: mun:mod-remainder a := n, m := 3, r := n mod 3, from 5.1, 5.2
      obtain ⟨q, s5_4⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := n) (m := (3 : ℤ)) (by parley_side) (r := n % (3 : ℤ)) (by parley_side) s5_2)).mp (by parley_side)
      -- 5.5. algebra, from 5.4
      have s5_5 : q * 3 = n - n % (3 : ℤ) := by linear_combination (norm := parley_norm) s5_4
      -- 5.6. inequalities, from H1
      have s5_6 : n ≥ 1 := by parley_order
      -- 5.7. inequalities
      have s5_7 : n - n % (3 : ℤ) > n - 3 := by parley_order
      -- 5.8. inequalities
      have s5_8 : n - 3 ≥ -2 := by parley_order
      -- 5.9. transitivity, from 5.5, 5.7, 5.8
      have s5_9 : q * 3 > -2 := by parley_order
      -- 5.10. inequalities
      have s5_10 : (q : ℚ) > -(2 / 3) := by parley_order
      -- 5.11. calculation
      have s5_11 : q > -1 := by
        try qify
        calc (q : ℚ) > -(2 / 3) := by parley_side
          _ > -1 := by norm_num
      -- 5.12. calculation
      have s5_12 : 0 ≤ q := by
        calc (0 : ℤ) = -1 + 1 := by norm_num
          _ ≤ q := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (-1 : ℤ)) (n := q) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (-1 : ℤ)) (n := q) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (-1 : ℤ)) (n := q) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (-1 : ℤ)) (n := q) (by parley_side)); parley_side)
      -- 5.13. mun:nat0-as-int n := q, from 5.12
      have s5_13 : 0 ≤ q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := q))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := q))).mpr (by parley_side); parley_side)
      -- 5.14. cases, from 5.3
      have s5_14 : (3 : ℤ) ∣ n := by
        rcases s5_3 with (hC1 | hC2) | hC3
        · skip
          -- 5.14.1. substitute n mod 3 = 0 (C1) into line 5.4
          have s5_14_1 : q * 3 = n := by parley_subst_at hC1 s5_4
          -- 5.14.2. algebra, from 5.14.1
          have s5_14_2 : n = 3 * q := by linear_combination (norm := parley_norm) (-1) * s5_14_1
          -- 5.14.3. def:divides d := 3, from 5.14.2
          have s5_14_3 : (3 : ℤ) ∣ n := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n))).mpr ⟨q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n))).mpr ⟨q, by parley_side⟩; parley_side)
          all_goals parley_side
        · skip
          -- 5.14.4. substitute n mod 3 = 1 (C2) into line 5.4
          have s5_14_4 : q * 3 + 1 = n := by parley_subst_at hC2 s5_4
          -- 5.14.5. algebra, from 5.14.4
          have s5_14_5 : n = 3 * q + 1 := by linear_combination (norm := parley_norm) (-1) * s5_14_4
          -- 5.14.6. instantiate k := q in line 4, from 5.13
          have s5_14_6 : (Even (F (3 * q)) ∧ Odd (F (3 * q + 1))) ∧ Odd (F (3 * q + 2)) := by first | exact (s4 q (by parley_side)) | exact ((s4 q (by parley_side))).symm | simpa using (s4 q (by parley_side)) | exact_mod_cast (s4 q (by parley_side)) | (have h := (s4 q (by parley_side)); parley_side)
          -- 5.14.7. instantiate k := 3q + 1 in line 2
          have r274_1 : 0 ≤ 3 * q + 1 := by parley_side
          -- 5.14.8. substitute n = 3q + 1 (line 5.14.5) into P1
          have s5_14_8 : Even (F (3 * q + 1)) := by parley_subst_at s5_14_5 hP1
          -- 5.14.9. mun:not-both n := F(3q + 1), from 5.14.8
          have s5_14_9 : ¬ Odd (F (3 * q + 1)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 1)) s5_14_8) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 1)) s5_14_8)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 1)) s5_14_8) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 1)) s5_14_8) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 1)) s5_14_8); parley_side)
          all_goals parley_side
        · skip
          -- 5.14.10. substitute n mod 3 = 2 (C3) into line 5.4
          have s5_14_10 : q * 3 + 2 = n := by parley_subst_at hC3 s5_4
          -- 5.14.11. algebra, from 5.14.10
          have s5_14_11 : n = 3 * q + 2 := by linear_combination (norm := parley_norm) (-1) * s5_14_10
          -- 5.14.12. instantiate k := q in line 4, from 5.13
          have s5_14_12 : (Even (F (3 * q)) ∧ Odd (F (3 * q + 1))) ∧ Odd (F (3 * q + 2)) := by first | exact (s4 q (by parley_side)) | exact ((s4 q (by parley_side))).symm | simpa using (s4 q (by parley_side)) | exact_mod_cast (s4 q (by parley_side)) | (have h := (s4 q (by parley_side)); parley_side)
          -- 5.14.13. instantiate k := 3q + 2 in line 2
          have r297_1 : 0 ≤ 3 * q + 2 := by parley_side
          -- 5.14.14. substitute n = 3q + 2 (line 5.14.11) into P1
          have s5_14_14 : Even (F (3 * q + 2)) := by parley_subst_at s5_14_11 hP1
          -- 5.14.15. mun:not-both n := F(3q + 2), from 5.14.14
          have s5_14_15 : ¬ Odd (F (3 * q + 2)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 2)) s5_14_14) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 2)) s5_14_14)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 2)) s5_14_14) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 2)) s5_14_14) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := F (3 * q + 2)) s5_14_14); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hP2
      -- 5.15. obtain k: def:divides d := 3, from P2
      obtain ⟨k, s5_15⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n))).mp (by parley_side)
      -- 5.16. inequalities, from H1
      have s5_16 : n ≥ 1 := by parley_order
      -- 5.17. transitivity, from 5.15, 5.16
      have s5_17 : 3 * k ≥ 1 := by parley_order
      -- 5.18. inequalities
      have s5_18 : (k : ℚ) ≥ 1 / 3 := by parley_order
      -- 5.19. calculation
      have s5_19 : k > 0 := by
        try qify
        calc (k : ℚ) ≥ 1 / 3 := by parley_side
          _ > 0 := by norm_num
      -- 5.20. mun:pos-int-nat m := k, from 5.19
      have s5_20 : 0 < k := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)); parley_side)
      -- 5.21. instantiate k := k in line 4, from 5.20
      have s5_21 : (Even (F (3 * k)) ∧ Odd (F (3 * k + 1))) ∧ Odd (F (3 * k + 2)) := by first | exact (s4 k (by parley_side)) | exact ((s4 k (by parley_side))).symm | simpa using (s4 k (by parley_side)) | exact_mod_cast (s4 k (by parley_side)) | (have h := (s4 k (by parley_side)); parley_side)
      -- 5.22. substitute n = 3·k (line 5.15) into line 5.21
      have s5_22 : Even (F n) := by parley_subst_at s5_15 s5_21
      all_goals parley_side
  all_goals exact s5

end Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.FibonacciEvenIffThreeDivides
