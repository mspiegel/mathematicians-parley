module

public import Divisibility
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-rules.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderRules.RemainderOfProduct

theorem remainder_of_product (A : ℝ) (B : ℤ) (M : ℝ) (hH4 : M > 0) :
    LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M * (B : ℝ)) M = LeanBridges.Divisibility.mod (A * (B : ℝ)) M := by
  -- 1. inequalities
  have s1 : M ≠ 0 := by parley_side
  set q : ℤ := ⌊A / M⌋ with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)); parley_side)
  -- 2. mun:mod-value a := A, b := M, from D1, H4
  have s2 : LeanBridges.Divisibility.mod A M = A - M * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) (by parley_side)); parley_side)
  -- 3. algebra, from 2
  have s3 : LeanBridges.Divisibility.mod A M * (B : ℝ) = A * (B : ℝ) + M * -((q : ℝ) * (B : ℝ)) := by linear_combination (norm := parley_norm) ((B : ℝ)) * s2
  -- 4. calculation
  have s4 : LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M * (B : ℝ)) M = LeanBridges.Divisibility.mod (A * (B : ℝ)) M := by
    calc LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M * (B : ℝ)) M = LeanBridges.Divisibility.mod (A * (B : ℝ) + M * -((q : ℝ) * (B : ℝ))) M := by parley_subst s3
      _ = LeanBridges.Divisibility.mod (A * (B : ℝ)) M := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B)))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) hH4 (K := -(q * B))); parley_side)
  all_goals exact s4

end Parley.Proofs.Setmm.RemainderRules.RemainderOfProduct
