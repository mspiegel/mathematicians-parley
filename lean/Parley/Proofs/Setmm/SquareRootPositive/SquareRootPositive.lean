module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/square-root-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareRootPositive.SquareRootPositive

theorem square_root_positive (a : ℝ) (hH2 : 0 < a) :
    0 < Real.sqrt a := by
  -- 1. def:sqrt x := a
  have r10_1 : 0 ≤ a := by parley_side
  have s1a : Real.sqrt a ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side)); parley_side)
  have s1b : Real.sqrt a ^ 2 = a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); parley_side)
  -- 2. contradiction
  have s2 : 0 < Real.sqrt a := by
    by_contra hc_hS
    have hS : ¬ 0 < Real.sqrt a := by parley_suppose hc_hS
    -- 2.1. inequalities, from S
    have s2_1 : Real.sqrt a ≤ 0 := by parley_order
    -- 2.2. inequalities, from 1
    have s2_2 : Real.sqrt a ≥ 0 := by parley_order
    -- 2.3. antisymmetry, from 2.1, 2.2
    have s2_3 : Real.sqrt a = 0 := by parley_side
    -- 2.4. algebra, from 2.3
    have s2_4 : Real.sqrt a ^ 2 = 0 := by linear_combination (norm := parley_norm) (Real.sqrt a) * s2_3
    -- 2.5. transitivity, from 1, 2.4
    have s2_5 : a = 0 := by parley_side
    -- 2.6. inequalities
    have s2_6 : a ≤ 0 := by parley_order
    -- 2.7. inequalities, from 2.6
    have s2_7 : ¬ 0 < a := by parley_side
    all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.SquareRootPositive.SquareRootPositive
