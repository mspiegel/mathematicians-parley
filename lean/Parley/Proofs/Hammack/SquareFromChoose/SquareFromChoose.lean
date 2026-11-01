module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Proofs.Hammack.SquareFromChoose.ChooseOne

/-! Written from proofs/hammack/square-from-choose.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareFromChoose.SquareFromChoose

theorem square_from_choose (n : ℕ) (hH1 : 0 < n) :
    (n : ℤ) ^ 2 = 2 * (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (n : ℤ) (1 : ℤ) : ℤ) := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℕ, 0 < m → (m : ℤ) ^ 2 = 2 * (Parley.Library.choose (m : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (m : ℤ) (1 : ℤ) : ℤ) := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) < 2 := by parley_arith
      -- 1.2. def:C n := 1, k := 2, from 1.1
      have s1_2 : (Parley.Library.choose (1 : ℤ) (2 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (2 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (2 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (2 : ℤ))) (by parley_side)).symm
      -- 1.3. thm:choose-one n := 1
      have s1_3 : (Parley.Library.choose (1 : ℤ) (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := 1) (by parley_side)) | (have h := (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := 1) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := 1) (by parley_side))).symm
      -- 1.4. algebra, from 1.2, 1.3
      have s1_4 : 1 ^ 2 = 2 * (Parley.Library.choose (1 : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (1 : ℤ) (1 : ℤ) : ℤ) := by linear_combination (norm := parley_norm) (-2) * s1_2 + (-1) * s1_3
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.5. thm:pascal n := m, k := 2
      have s1_5 : (Parley.Library.choose (m : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (m : ℤ) (2 - 1 : ℤ) : ℤ) = (Parley.Library.choose ((m : ℤ) + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := m) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := m) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := m) (k := (2 : ℤ)))).symm
      -- 1.6. substitute 2 − 1 = 1 (arithmetic) into line 1.5
      have s1_6 : (Parley.Library.choose (m : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (m : ℤ) (1 : ℤ) : ℤ) = (Parley.Library.choose ((m : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1_5
      -- 1.7. thm:choose-one n := m
      have s1_7 : (Parley.Library.choose (m : ℤ) (1 : ℤ) : ℤ) = (m : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m) (by parley_side)) | (have h := (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m) (by parley_side))).symm
      -- 1.8. thm:choose-one n := m + 1
      have s1_8 : (Parley.Library.choose ((m : ℤ) + 1) (1 : ℤ) : ℤ) = (m : ℤ) + 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m + 1) (by parley_side)) | (have h := (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m + 1) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m + 1) (by parley_side))).symm
      -- 1.9. algebra, from IH, 1.6, 1.7, 1.8
      have s1_9 : ((m : ℤ) + 1) ^ 2 = 2 * (Parley.Library.choose ((m : ℤ) + 1) (2 : ℤ) : ℤ) + (Parley.Library.choose ((m : ℤ) + 1) (1 : ℤ) : ℤ) := by linear_combination (norm := parley_norm) hIH + (2) * s1_6 + (-1) * s1_7 + (-1) * s1_8
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : (n : ℤ) ^ 2 = 2 * (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (n : ℤ) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm
  all_goals parley_side

end Parley.Proofs.Hammack.SquareFromChoose.SquareFromChoose
