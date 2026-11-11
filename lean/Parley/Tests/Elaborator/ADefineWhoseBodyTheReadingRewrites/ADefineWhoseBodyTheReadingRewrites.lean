module

public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-define-whose-body-the-reading-rewrites.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineWhoseBodyTheReadingRewrites.ADefineWhoseBodyTheReadingRewrites

theorem a_define_whose_body_the_reading_rewrites (r : ℝ) (a : ℝ) (hH3 : abs a = r) :
    a ∈ {x : ℝ | abs x = r} := by
  set C : Set ℝ := {x : ℝ | abs x = r} with hD1
  -- 1. def:set-builder u := a, from D1, H3
  have hI : a ∈ {t : ℝ | abs t = r} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℝ => abs x = r)) (X := (Set.univ : Set ℝ)) (u := a))).mpr ⟨by parley_set_side, hH3⟩)
  exact hI

end Parley.Tests.Elaborator.ADefineWhoseBodyTheReadingRewrites.ADefineWhoseBodyTheReadingRewrites
