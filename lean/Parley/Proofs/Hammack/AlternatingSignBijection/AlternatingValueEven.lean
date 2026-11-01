module

public import Parley.Library
public import Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven

theorem alternating_value_even (f : ℕ → ℤ) (hH2 : ∀ n : ℕ, 0 < n → (f n : ℚ) = ((-1) ^ n * (2 * (n : ℚ) - 1) + 1) / 4) (m : ℕ) (hH3 : 0 < m) (hH4 : Even (m : ℤ)) :
    (f m : ℚ) = (m : ℚ) / 2 := by
  -- 1. thm:sign-of-even n := m, from H4
  have s1 : ((-1) ^ m : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) (by parley_side))).symm
  -- 2. calculation
  have s2 : (f m : ℚ) = (m : ℚ) / 2 := by
    calc (f m : ℚ) = ((-1) ^ m * (2 * (m : ℚ) - 1) + 1) / 4 := by first | linear_combination (norm := parley_norm) (hH2 m (by parley_side)) | (have h := (hH2 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (hH2 m (by parley_side)) | exact_mod_cast ((hH2 m (by parley_side))).symm
      _ = (1 * (2 * (m : ℚ) - 1) + 1) / 4 := by
          have s1_w : ((-1) ^ m : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination h
          parley_subst s1_w
      _ = (m : ℚ) / 2 := by parley_ring
  all_goals parley_side

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven
