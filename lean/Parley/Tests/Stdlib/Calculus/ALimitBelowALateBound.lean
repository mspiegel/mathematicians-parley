module

public import Tactics
public import Parley.Stdlib.Calculus.LimitAtMost

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ALimitBelowALateBound

theorem a_limit_below_a_late_bound (y : ℤ → ℝ) (M : ℝ) (hH3 : Filter.Tendsto (fun n : ℕ => (y (n : ℤ) : ℝ)) Filter.atTop (nhds M)) (C : ℝ) (K : ℕ) (hH5 : 0 < K) (hH6 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (K : ℝ) → y (n : ℤ) ≤ C) :
    M ≤ C := by
  -- 1. thm:limit-at-most x := y, L := M, B := C, N := K, from H3, H6
  have s1 : M ≤ C := by first | linarith [(Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side))] | (have h := (Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side)) | (have h := (Parley.Stdlib.Calculus.LimitAtMost.limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.ALimitBelowALateBound
