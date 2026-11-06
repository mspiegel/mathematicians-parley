module

public import AlgebraTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/compose-rational-and-line.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ComposeRationalAndLine.ComposeRationalAndLine

theorem compose_rational_and_line (f : ℝ → ℝ) (g : ℝ → ℝ) (hH3 : ∀ x : ℝ, f x = 1 / (x ^ 2 + 1)) (hH4 : ∀ x : ℝ, g x = 3 * x + 2) :
    (∀ x : ℝ, (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 ∧ (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1)) := by
  -- 1. proof
  have s1 : ∀ x : ℝ, (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 ∧ (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1) := by
    intro x
    -- 1.1. mun:function-value
    -- 1.2. mun:square-nonneg
    have s1_2 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side)
    -- 1.3. inequalities, from 1.2
    have s1_3 : x ^ 2 + 1 > 0 := by parley_order
    -- 1.4. calculation
    have r27_1 : x ^ 2 + 1 ≠ 0 := by parley_set_side
    have s1_4 : (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 := by
      calc (g ∘ f) x = g (f x) := by first | exact (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := f) (g := g) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := f) (g := g) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := f) (g := g) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := f) (g := g) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := f) (g := g) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)); parley_set_side)
        _ = 3 * f x + 2 := by first | linear_combination (norm := parley_norm) (hH4 (f x)) | (have h := (hH4 (f x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH4 (f x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH4 (f x)) | exact_mod_cast ((hH4 (f x))).symm | (have h := (hH4 (f x)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH4 (f x)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH4 (f x)); parley_int_power h) | (have h := (hH4 (f x)); parley_set_side)
        _ = 3 * (1 / (x ^ 2 + 1)) + 2 := by parley_subst hH3
        _ = 3 / (x ^ 2 + 1) + 2 := by parley_ring
    -- 1.5. mun:function-value f := g
    -- 1.6. calculation
    have s1_6 : (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1) := by
      calc (f ∘ g) x = f (g x) := by first | exact (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := g) (g := f) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := g) (g := f) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := g) (g := f) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := g) (g := f) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_composition_value (Y := (Set.univ : Set ℝ)) (X := (Set.univ : Set ℝ)) (f := g) (g := f) (x := x) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_set_side)); parley_set_side)
        _ = 1 / (g x ^ 2 + 1) := by first | linear_combination (norm := parley_norm) (hH3 (g x)) | (have h := (hH3 (g x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH3 (g x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH3 (g x)) | exact_mod_cast ((hH3 (g x))).symm | (have h := (hH3 (g x)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH3 (g x)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH3 (g x)); parley_int_power h) | (have h := (hH3 (g x)); parley_set_side)
        _ = 1 / ((3 * x + 2) ^ 2 + 1) := by parley_subst hH4
    -- 1.7. join 1.4, 1.6
    have s1_7a : (g ∘ f) x = 3 / (x ^ 2 + 1) + 2 := by parley_set_side
    have s1_7b : (f ∘ g) x = 1 / ((3 * x + 2) ^ 2 + 1) := by parley_set_side
    all_goals parley_set_side
  all_goals exact s1

end Parley.Proofs.Hammack.ComposeRationalAndLine.ComposeRationalAndLine
