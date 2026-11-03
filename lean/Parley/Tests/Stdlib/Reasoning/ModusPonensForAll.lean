module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.ModusPonensForAll

theorem modus_ponens_for_all (n : ℕ) (hH1 : 0 < n) (hH2 : (n : ℤ) ≤ 3 → (∀ x : ℝ, x ≠ 0 → x ^ 2 > 0)) (hH3 : (n : ℤ) ≤ 3) :
    (∀ x : ℝ, x ≠ 0 → x ^ 2 > 0) := by
  -- 1. mun:reasoning-modus-ponens, from H2, H3
  have s1 : ∀ x : ℝ, x ≠ 0 → x ^ 2 > 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (n : ℤ) ≤ 3) (Q := ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2) (by parley_side) hH3) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (n : ℤ) ≤ 3) (Q := ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2) (by parley_side) hH3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (n : ℤ) ≤ 3) (Q := ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2) (by parley_side) hH3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (n : ℤ) ≤ 3) (Q := ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2) (by parley_side) hH3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (n : ℤ) ≤ 3) (Q := ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2) (by parley_side) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.ModusPonensForAll
