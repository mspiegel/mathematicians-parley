module

public import Tactics
public import Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd

theorem alternating_value_odd (f : ℤ → ℤ) (hH2 : ∀ n : ℕ, 0 < n → (f (n : ℤ) : ℚ) = ((-1) ^ n * (2 * (n : ℚ) - 1) + 1) / 4) (m : ℕ) (hH3 : 0 < m) (hH4 : Odd (m : ℤ)) :
    (f (m : ℤ) : ℚ) = (1 - (m : ℚ)) / 2 := by
  -- 1. thm:sign-of-odd n := m, from H4
  have s1 : ((-1) ^ m : ℤ) = -1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd.sign_of_odd (n := m) (by parley_side) (by parley_side)); parley_side)
  -- 2. calculation
  have s2 : (f (m : ℤ) : ℚ) = (1 - (m : ℚ)) / 2 := by
    calc (f (m : ℤ) : ℚ) = ((-1) ^ m * (2 * (m : ℚ) - 1) + 1) / 4 := by first | linear_combination (norm := parley_norm) (hH2 m (by parley_side)) | (have h := (hH2 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 m (by parley_side)) | exact_mod_cast ((hH2 m (by parley_side))).symm | (have h := (hH2 m (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); parley_int_power h) | (have h := (hH2 m (by parley_side)); parley_side)
      _ = (-1 * (2 * (m : ℚ) - 1) + 1) / 4 := by
          have s1_w : ((-1) ^ m : ℚ) = -1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s1_w | parley_subst s1
      _ = (1 - (m : ℚ)) / 2 := by parley_ring
  all_goals exact s2

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd
