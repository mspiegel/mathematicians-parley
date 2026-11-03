module

public import Tactics
public import Parley.Proofs.Setmm.LimitUnique.LimitAtMost

/-! Written from proofs/setmm/limit-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitUnique.LimitUnique

theorem limit_unique (x : ℤ → ℝ) (A : ℝ) (B : ℝ) (hH4 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds A)) (hH5 : Filter.Tendsto (fun n : ℕ => (x (n : ℤ) : ℝ)) Filter.atTop (nhds B)) :
    A = B := by
  -- 1. thm:limit-at-most, from H4, H5
  have s1 : A ≤ B := by first | linarith [(Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := A) (B := B) hH4 hH5)] | (have h := (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := A) (B := B) hH4 hH5); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := A) (B := B) hH4 hH5) | (have h := (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := A) (B := B) hH4 hH5); parley_side)
  -- 2. thm:limit-at-most A := B, B := A, from H4, H5
  have s2 : B ≤ A := by first | linarith [(Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := B) (B := A) hH5 hH4)] | (have h := (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := B) (B := A) hH5 hH4); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := B) (B := A) hH5 hH4) | (have h := (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := B) (B := A) hH5 hH4); parley_side)
  -- 3. antisymmetry, from 1, 2
  have s3 : A = B := by parley_side
  all_goals exact s3

end Parley.Proofs.Setmm.LimitUnique.LimitUnique
