module

public import Tactics
public import Parley.Stdlib.Calculus.LimitAtMost

/-! Written from tests/elaborator/a-sequence-given-as-a-map.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOfALetter

theorem a_late_bound_of_a_letter (y : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℕ => (y (n : ℤ) : ℝ)) Filter.atTop (nhds L)) (hH4 : ∀ i : ℕ, 0 < i → (i : ℝ) ≥ 1 → y (i : ℤ) ≤ 1) :
    L ≤ 1 := by
  -- 1. thm:limit-at-most x := y, B := 1, N := 1, from H3, H4
  have s1 : L ≤ 1 := by first | linarith [(Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := 1) (by parley_side) (by parley_side))] | (have h := (Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := 1) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := 1) (by parley_side) (by parley_side)) | (have h := (Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := 1) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOfALetter
