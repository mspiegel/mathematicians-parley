module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from proofs/setmm/identity-function-continuous.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IdentityFunctionContinuous.IdentityFunctionContinuous

theorem identity_function_continuous (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (f : ℝ → ℝ) (hH2 : Set.MapsTo f D (Set.univ : Set ℝ)) (hH3 : ∀ x ∈ D, f x = x) :
    ContinuousOn f D := by
  -- 1. proof
  have s1 : ∀ a ∈ D, ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε)) := by
    intro a hK1
    -- 1.1. proof
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε)) := by
      intro ε
      intro hA1
      -- 1.1.1. proof
      have s1_1_1 : ∀ x ∈ D, abs (x - a) < ε → abs (f x - f a) < ε := by
        intro x hK3
        intro hA2
        -- 1.1.1.1. instantiate x := x in H3, from K3
        have s1_1_1_1 : f x = x := by first | linear_combination (norm := parley_norm) (hH3 x (by parley_set_side)) | (have h := (hH3 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH3 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH3 x (by parley_set_side)) | exact_mod_cast ((hH3 x (by parley_set_side))).symm | (have h := (hH3 x (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH3 x (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH3 x (by parley_set_side)); parley_int_power h) | (have h := (hH3 x (by parley_set_side)); parley_set_side)
        -- 1.1.1.2. instantiate x := a in H3, from K1
        have s1_1_1_2 : f a = a := by first | linear_combination (norm := parley_norm) (hH3 a (by parley_set_side)) | (have h := (hH3 a (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH3 a (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH3 a (by parley_set_side)) | exact_mod_cast ((hH3 a (by parley_set_side))).symm | (have h := (hH3 a (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH3 a (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH3 a (by parley_set_side)); parley_int_power h) | (have h := (hH3 a (by parley_set_side)); parley_set_side)
        -- 1.1.1.3. calculation
        have s1_1_1_3 : f x - f a = x - a := by
          calc f x - f a = x - f a := by parley_subst s1_1_1_1
            _ = x - a := by parley_subst s1_1_1_2
        -- 1.1.1.4. calculation
        have s1_1_1_4 : abs (f x - f a) < ε := by
          calc abs (f x - f a) = abs (x - a) := by parley_subst s1_1_1_3
            _ < ε := by parley_set_side
        all_goals parley_set_side
      -- 1.1.2. exhibit, from A1, 1.1.1
      have s1_1_2 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε) := ⟨ε, ⟨by parley_set_side, by parley_set_side⟩⟩
      all_goals parley_set_side
    all_goals exact s1_1
  -- 2. def:continuous-on, from H1, 1
  have s2 : ContinuousOn f D := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := D) (by parley_set_side) hH1)).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := D) (by parley_set_side) hH1)).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.IdentityFunctionContinuous.IdentityFunctionContinuous
