module

public import ArithTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/constant-function-continuous.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ConstantFunctionContinuous.ConstantFunctionContinuous

theorem constant_function_continuous (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (k : ℝ) (f : ℝ → ℝ) (hH3 : Set.MapsTo f D (Set.univ : Set ℝ)) (hH4 : ∀ x ∈ D, f x = k) :
    ContinuousOn f D := by
  -- 1. proof
  have s1 : ∀ a ∈ D, ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε)) := by
    intro a hK1
    -- 1.1. proof
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε)) := by
      intro ε
      intro hA1
      -- 1.1.1. proof
      have s1_1_1 : ∀ x ∈ D, abs (x - a) < 1 → abs (f x - f a) < ε := by
        intro x hK3
        intro hA2
        -- 1.1.1.1. instantiate x := x in H4, from K3
        have s1_1_1_1 : f x = k := by first | linear_combination (norm := parley_norm) (hH4 x (by parley_set_side)) | (have h := (hH4 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH4 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH4 x (by parley_set_side)) | exact_mod_cast ((hH4 x (by parley_set_side))).symm | (have h := (hH4 x (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH4 x (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH4 x (by parley_set_side)); parley_int_power h) | (have h := (hH4 x (by parley_set_side)); parley_set_side)
        -- 1.1.1.2. instantiate x := a in H4, from K1
        have s1_1_1_2 : f a = k := by first | linear_combination (norm := parley_norm) (hH4 a (by parley_set_side)) | (have h := (hH4 a (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH4 a (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH4 a (by parley_set_side)) | exact_mod_cast ((hH4 a (by parley_set_side))).symm | (have h := (hH4 a (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH4 a (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH4 a (by parley_set_side)); parley_int_power h) | (have h := (hH4 a (by parley_set_side)); parley_set_side)
        -- 1.1.1.3. algebra, from 1.1.1.1, 1.1.1.2
        have s1_1_1_3 : f x - f a = 0 := by linear_combination (norm := parley_norm) s1_1_1_1 + (-1) * s1_1_1_2
        -- 1.1.1.4. calculation
        have s1_1_1_4 : abs (f x - f a) < ε := by
          calc abs (f x - f a) = abs 0 := by parley_subst s1_1_1_3
            _ = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Numbers.mun_abs_zero | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Numbers.mun_abs_zero | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_zero).symm | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; parley_int_power h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; parley_set_side)
            _ < ε := by parley_set_side
        all_goals parley_set_side
      -- 1.1.2. exhibit, from 1.1.1
      have r45_1 : (1 : ℝ) > 0 := by parley_arith
      have s1_1_2 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, abs (x - a) < δ → abs (f x - f a) < ε) := ⟨(1 : ℝ), ⟨by parley_set_side, by parley_set_side⟩⟩
      all_goals parley_set_side
    all_goals exact s1_1
  -- 2. def:continuous-on, from H1, 1
  have s2 : ContinuousOn f D := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := D) (by parley_set_side) hH1)).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := D) (by parley_set_side) hH1)).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.ConstantFunctionContinuous.ConstantFunctionContinuous
