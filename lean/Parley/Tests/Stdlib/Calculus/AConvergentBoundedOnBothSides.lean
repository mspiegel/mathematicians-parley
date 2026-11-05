module

public import Tactics
public import Parley.Stdlib.Calculus.ConvergentAbsBounded

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AConvergentBoundedOnBothSides

theorem a_convergent_bounded_on_both_sides (y : ℤ → ℝ) (M : ℝ) (hH3 : Filter.Tendsto (fun n : ℕ => (y (n : ℤ) : ℝ)) Filter.atTop (nhds M)) :
    (∃ B : ℝ, ∀ m : ℕ, 0 < m → abs (y (m : ℤ)) ≤ B) := by
  -- 1. thm:convergent-abs-bounded x := y, L := M, from H3
  have s1 : ∃ B : ℝ, ∀ m : ℕ, 0 < m → abs (y (m : ℤ)) ≤ B := by first | exact (Parley.Stdlib.Calculus.ConvergentAbsBounded.convergent_abs_bounded (x := y) (L := M) hH3) | exact ((Parley.Stdlib.Calculus.ConvergentAbsBounded.convergent_abs_bounded (x := y) (L := M) hH3)).symm | simpa using (Parley.Stdlib.Calculus.ConvergentAbsBounded.convergent_abs_bounded (x := y) (L := M) hH3) | exact_mod_cast (Parley.Stdlib.Calculus.ConvergentAbsBounded.convergent_abs_bounded (x := y) (L := M) hH3) | (have h := (Parley.Stdlib.Calculus.ConvergentAbsBounded.convergent_abs_bounded (x := y) (L := M) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AConvergentBoundedOnBothSides
