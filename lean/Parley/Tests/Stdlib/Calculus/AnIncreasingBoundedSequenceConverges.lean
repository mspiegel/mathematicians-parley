module

public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnIncreasingBoundedSequenceConverges

theorem an_increasing_bounded_sequence_converges (y : ℤ → ℝ) (hH2 : ∀ m : ℕ, 0 < m → y (m : ℤ) ≤ y ((m : ℤ) + 1)) (C : ℝ) (hH4 : ∀ m : ℕ, 0 < m → y (m : ℤ) ≤ C) :
    (∃ M : ℝ, Filter.Tendsto (fun n : ℕ => (y (n : ℤ) : ℝ)) Filter.atTop (nhds M)) := by
  -- 1. thm:monotone-limit x := y, B := C, from H2, H4
  have s1 : ∃ M : ℝ, Filter.Tendsto (fun n : ℕ => (y (n : ℤ) : ℝ)) Filter.atTop (nhds M) := by first | exact (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := y) (by parley_side) (B := C) (by parley_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := y) (by parley_side) (B := C) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := y) (by parley_side) (B := C) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := y) (by parley_side) (B := C) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := y) (by parley_side) (B := C) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AnIncreasingBoundedSequenceConverges
