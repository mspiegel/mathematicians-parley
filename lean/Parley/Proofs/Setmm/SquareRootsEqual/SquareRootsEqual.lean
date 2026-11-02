module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/square-roots-equal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareRootsEqual.SquareRootsEqual

theorem square_roots_equal (a : ℝ) (b : ℝ) (hH3 : 0 ≤ a) (hH4 : 0 ≤ b) :
    (Real.sqrt a = Real.sqrt b ↔ a = b) := by
  -- 1. def:sqrt x := a
  have r12_1 : a ≥ 0 := by parley_side
  have s1 : Real.sqrt a ^ 2 = a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); parley_side)
  -- 2. both directions
  have s2 : Real.sqrt a = Real.sqrt b ↔ a = b := by
    constructor
    · skip
      intro hD1
      -- 2.1. substitute √a = √b (D1) into line 1
      have s2_1 : Real.sqrt b ^ 2 = a := by parley_subst_at hD1 s1
      -- 2.2. calculation
      have r25_1 : b ≥ 0 := by parley_side
      have s2_2 : a = b := by
        calc a = Real.sqrt b ^ 2 := by parley_side
          _ = b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 2.3. substitute a = b (D2)
      have s2_3 : Real.sqrt a = Real.sqrt b := by parley_subst hD2
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.SquareRootsEqual.SquareRootsEqual
