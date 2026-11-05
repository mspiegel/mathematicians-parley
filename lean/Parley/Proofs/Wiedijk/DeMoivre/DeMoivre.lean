module

public import AlgebraTactics
public import ComplexTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/wiedijk/de-moivre.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DeMoivre.DeMoivre

set_option maxHeartbeats 400000 in
theorem de_moivre (x : ℝ) (n : ℕ) :
    (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ n = Complex.cos ((n : ℂ) * (x : ℂ)) + Complex.I * Complex.sin ((n : ℂ) * (x : ℂ)) := by
  -- 1. def:i
  have s1 : Complex.I * Complex.I = -1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Numbers.def_i | (have h := Parley.Items.Stdlib.Numbers.def_i; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.def_i; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Numbers.def_i | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_i).symm | (have h := Parley.Items.Stdlib.Numbers.def_i; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.def_i; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.def_i; parley_int_power h) | (have h := Parley.Items.Stdlib.Numbers.def_i; parley_side)
  -- 2. induction on k starting at 0
  have s2 : ∀ k : ℕ, (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ k = Complex.cos ((k : ℂ) * (x : ℂ)) + Complex.I * Complex.sin ((k : ℂ) * (x : ℂ)) := by
    intro k
    induction k with
    | zero =>
      -- 2.1. algebra
      have s2_1 : 0 * x = 0 := by parley_ring
      -- 2.2. substitute cos(0) = 1 (real arithmetic)
      have s2_2 : Complex.cos (0 : ℂ) + Complex.I * Complex.sin (0 : ℂ) = 1 + Complex.I * Complex.sin (0 : ℂ) := by parley_subst (show Complex.cos (0 : ℂ) = 1 by parley_real)
      -- 2.3. substitute sin(0) = 0 (real arithmetic)
      have s2_3 : 1 + Complex.I * Complex.sin (0 : ℂ) = 1 + Complex.I * 0 := by parley_subst (show Complex.sin (0 : ℂ) = 0 by parley_real)
      -- 2.4. calculation
      have s2_4 : (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ 0 = Complex.cos (0 * (x : ℂ)) + Complex.I * Complex.sin (0 * (x : ℂ)) := by
        calc (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ 0 = 1 := by parley_ring
          _ = 1 + Complex.I * 0 := by parley_ring
          _ = 1 + Complex.I * Complex.sin (0 : ℂ) := by parley_side
          _ = Complex.cos (0 : ℂ) + Complex.I * Complex.sin (0 : ℂ) := by parley_side
          _ = Complex.cos (0 * (x : ℂ)) + Complex.I * Complex.sin (0 * (x : ℂ)) := by
              have s2_1_w : 0 * (x : ℂ) = 0 := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_1; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_1_w | parley_subst s2_1
      all_goals parley_side
    | succ k hIH =>
      -- 2.5. thm:cos-add a := k·x, b := x
      have s2_5 : Real.cos ((k : ℝ) * x + x) = Real.cos ((k : ℝ) * x) * Real.cos x - Real.sin ((k : ℝ) * x) * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_side)
      -- 2.6. thm:sin-add a := k·x, b := x
      have s2_6 : Real.sin ((k : ℝ) * x + x) = Real.sin ((k : ℝ) * x) * Real.cos x + Real.cos ((k : ℝ) * x) * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_side)
      -- 2.7. algebra
      have s2_7 : (k : ℝ) * x + x = ((k : ℝ) + 1) * x := by parley_ring
      -- 2.8. calculation
      have s2_8 : (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ (k + 1) = Complex.cos (((k : ℂ) + 1) * (x : ℂ)) + Complex.I * Complex.sin (((k : ℂ) + 1) * (x : ℂ)) := by
        calc (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ (k + 1) = (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ k * (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) (m := k)); parley_side)
          _ = (Complex.cos ((k : ℂ) * (x : ℂ)) + Complex.I * Complex.sin ((k : ℂ) * (x : ℂ))) * (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) := by parley_subst hIH
          _ = Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.I * (Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ)) + Complex.I * Complex.I * (Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ)) := by parley_ring
          _ = Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.I * (Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ)) + -1 * (Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ)) := by parley_subst s1
          _ = Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) - Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ) + Complex.I * (Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ)) := by parley_ring
          _ = Complex.cos ((k : ℂ) * (x : ℂ) + (x : ℂ)) + Complex.I * (Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ)) := by
              have s2_5_w : Complex.cos ((k : ℂ) * (x : ℂ) + (x : ℂ)) = Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) - Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_5_w | parley_subst s2_5
          _ = Complex.cos ((k : ℂ) * (x : ℂ) + (x : ℂ)) + Complex.I * Complex.sin ((k : ℂ) * (x : ℂ) + (x : ℂ)) := by
              have s2_6_w : Complex.sin ((k : ℂ) * (x : ℂ) + (x : ℂ)) = Complex.sin ((k : ℂ) * (x : ℂ)) * Complex.cos (x : ℂ) + Complex.cos ((k : ℂ) * (x : ℂ)) * Complex.sin (x : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_6; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_6_w | parley_subst s2_6
          _ = Complex.cos (((k : ℂ) + 1) * (x : ℂ)) + Complex.I * Complex.sin (((k : ℂ) + 1) * (x : ℂ)) := by
              have s2_7_w : (k : ℂ) * (x : ℂ) + (x : ℂ) = ((k : ℂ) + 1) * (x : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_7; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_7_w | parley_subst s2_7
      all_goals parley_side
  -- 3. instantiate k := n in line 2
  have s3 : (Complex.cos (x : ℂ) + Complex.I * Complex.sin (x : ℂ)) ^ n = Complex.cos ((n : ℂ) * (x : ℂ)) + Complex.I * Complex.sin ((n : ℂ) * (x : ℂ)) := by first | linear_combination (norm := parley_norm) (s2 n) | (have h := (s2 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s2 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s2 n) | exact_mod_cast ((s2 n)).symm | (have h := (s2 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s2 n); qify; linear_combination (norm := parley_norm) h) | (have h := (s2 n); parley_int_power h) | (have h := (s2 n); parley_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.DeMoivre.DeMoivre
