module

public import Divisibility
public import NormTactics
public import PowerTactics
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

namespace Parley.Proofs.Setmm.RemainderRules.RemainderOfSum

theorem remainder_of_sum (A : ℝ) (B : ℝ) (M : ℝ) (hH4 : M > 0) :
    LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M + B) M = LeanBridges.Divisibility.mod (A + B) M := by
  -- 1. inequalities
  have s1 : M ≠ 0 := by parley_side
  set q : ℤ := ⌊A / M⌋ with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / M)); parley_side)
  -- 2. mun:mod-value a := A, b := M, from D1, H4
  have s2 : LeanBridges.Divisibility.mod A M = A - M * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) hH4)
  -- 3. algebra, from 2
  have s3 : LeanBridges.Divisibility.mod A M + B = A + B + M * -(q : ℝ) := by linear_combination (norm := parley_norm) s2
  -- 4. calculation
  calc LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M + B) M = LeanBridges.Divisibility.mod (A + B + M * -(q : ℝ)) M := by parley_subst s3
    _ = LeanBridges.Divisibility.mod (A + B) M := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)) | exact_mod_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q))).symm | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A + B) (M := M) (by parley_side) (K := -q)); parley_side)

end Parley.Proofs.Setmm.RemainderRules.RemainderOfSum
