module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/a-sequence-given-as-a-map.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOfALetter

theorem a_late_bound_of_a_letter (y : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (y n : ℝ)) Filter.atTop (nhds L)) (hH4 : ∀ i : ℤ, 0 < i → i ≥ 1 → y i ≤ 1) :
    L ≤ 1 := by
  -- 1. thm:limit-at-most x := y, B := 1, N := 1, from H3, H4
  have s1 : L ≤ 1 := by first | linarith [(Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := (1 : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := (1 : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := (1 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := (1 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOfALetter
