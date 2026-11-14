module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-define-whose-body-the-reading-rewrites.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineWhoseBodyTheReadingRewrites.ADefineWhoseBodyTheReadingRewrites

theorem a_define_whose_body_the_reading_rewrites (r : ℝ) (a : ℝ) (hH3 : abs a = r) :
    a ∈ {x : ℝ | abs x = r} := by
  set C : Set ℝ := {x : ℝ | abs x = r} with hD1
  -- 1. def:set-builder u := a, from D1, H3
  have hI : a ∈ {t : ℝ | abs t = r} := by (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => abs x = r)) (X := (Set.univ : Set ℝ)) (u := a))).mpr ⟨Set.mem_univ _, hH3⟩); simp only [Set.mem_univ, true_and] at h; exact h)
  exact hI

end Parley.Tests.Elaborator.ADefineWhoseBodyTheReadingRewrites.ADefineWhoseBodyTheReadingRewrites
