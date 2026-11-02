module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.IncreasingTerms

theorem increasing_terms (x : ℤ → ℝ) (hH2 : ∀ n : ℕ, 0 < n → x (n : ℤ) ≤ x ((n : ℤ) + 1)) :
    (∀ n : ℕ, 0 < n → (∀ m : ℕ, 0 < m → (m : ℤ) ≤ (n : ℤ) → x (m : ℤ) ≤ x (n : ℤ))) := by
  -- 1. induction on n starting at 1
  have s1 : ∀ n : ℕ, 0 < n → (∀ m : ℕ, 0 < m → (m : ℤ) ≤ (n : ℤ) → x (m : ℤ) ≤ x (n : ℤ)) := by
    intro n h_n
    replace h_n : 1 ≤ n := h_n
    induction n, h_n using Nat.le_induction with
    | base =>
      intro m hK1
      intro hA1
      -- 1.1. inequalities, from K1
      have s1_1 : 1 ≤ (m : ℤ) := by parley_side
      -- 1.2. antisymmetry, from A1, 1.1
      have s1_2 : (m : ℤ) = 1 := by parley_side
      -- 1.3. substitute m = 1 (line 1.2)
      have s1_3 : x (m : ℤ) = x 1 := by
        have s1_2_w : (m : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1_2; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s1_2_w | parley_subst s1_2
      -- 1.4. inequalities
      have s1_4 : x (m : ℤ) ≤ x 1 := by parley_side
      all_goals parley_side
    | succ n hK hIH =>
      intro m hK1
      intro hA1
      -- 1.5. mun:le-cases x := m, y := n + 1, from A1
      have s1_5 : (m : ℤ) < (n : ℤ) + 1 ∨ (m : ℤ) = (n : ℤ) + 1 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (m : ℤ)) (y := (n : ℤ) + 1))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (m : ℤ)) (y := (n : ℤ) + 1))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (m : ℤ)) (y := (n : ℤ) + 1))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (m : ℤ)) (y := (n : ℤ) + 1))).mp (by parley_side)
      -- 1.6. cases, from 1.5
      have s1_6 : x (m : ℤ) ≤ x ((n : ℤ) + 1) := by
        rcases s1_5 with hC1 | hC2
        · skip
          -- 1.6.1. mun:integer-step n := n + 1, from C1
          have s1_6_1 : (m : ℤ) + 1 ≤ (n : ℤ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (m : ℤ)) (n := (n : ℤ) + 1) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (m : ℤ)) (n := (n : ℤ) + 1) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (m : ℤ)) (n := (n : ℤ) + 1) (by parley_side))
          -- 1.6.2. inequalities
          have s1_6_2 : (m : ℤ) ≤ (n : ℤ) := by parley_side
          -- 1.6.3. instantiate m := m in IH, from 1.6.2
          have s1_6_3 : x (m : ℤ) ≤ x (n : ℤ) := by first | linarith [(hIH m (by parley_side) (by parley_side))] | (have h := (hIH m (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hIH m (by parley_side) (by parley_side))
          -- 1.6.4. instantiate n := n in H2
          have s1_6_4 : x (n : ℤ) ≤ x ((n : ℤ) + 1) := by first | linarith [(hH2 n (by parley_side))] | (have h := (hH2 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH2 n (by parley_side))
          -- 1.6.5. transitivity, from 1.6.3, 1.6.4
          have s1_6_5 : x (m : ℤ) ≤ x ((n : ℤ) + 1) := by parley_side
          all_goals parley_side
        · skip
          -- 1.6.6. substitute m = n + 1 (C2)
          have s1_6_6 : x (m : ℤ) = x ((n : ℤ) + 1) := by
            have hC2_w : (m : ℝ) = (n : ℝ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) hC2; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst hC2_w | parley_subst hC2
          -- 1.6.7. inequalities
          have s1_6_7 : x (m : ℤ) ≤ x ((n : ℤ) + 1) := by parley_side
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Stdlib.Calculus.IncreasingTerms
