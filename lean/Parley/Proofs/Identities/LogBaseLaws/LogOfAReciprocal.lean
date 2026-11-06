module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.LogOfAReciprocal

theorem log_of_a_reciprocal (x : ℝ) (b : ℝ) (hH3 : x > 0) (hH4 : b > 0) (hH5 : b ≠ 1) :
    Real.log (1 / x) / Real.log b = -(Real.log x / Real.log b) := by
  -- 1. mun:ln-quotient x := 1, y := x, from H3
  have r61_1 : (1 : ℤ) > 0 := by parley_arith
  have s1 : Real.log (1 / x) = Real.log (1 : ℝ) - Real.log x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side)); parley_side)
  -- 2. substitute ln(1) = 0 (real arithmetic) into line 1
  have s2 : Real.log (1 / x) = 0 - Real.log x := by parley_subst_at (show Real.log (1 : ℝ) = 0 by parley_real) s1
  -- 3. mun:ln-nonzero x := b, from H4, H5
  have s3 : Real.log b ≠ 0 := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH5) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH5)).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH5) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH5) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH5); parley_side)
  -- 4. calculation
  have s4 : Real.log (1 / x) / Real.log b = -(Real.log x / Real.log b) := by
    calc Real.log (1 / x) / Real.log b = (0 - Real.log x) / Real.log b := by parley_subst s2
      _ = -(Real.log x / Real.log b) := by parley_ring
  all_goals exact s4

end Parley.Proofs.Identities.LogBaseLaws.LogOfAReciprocal
