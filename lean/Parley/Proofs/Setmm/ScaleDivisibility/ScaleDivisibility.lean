module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/scale-divisibility.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ScaleDivisibility.ScaleDivisibility

theorem scale_divisibility (M : ℤ) (N : ℤ) (K : ℤ) (H4 : M ∣ N) :
    K * M ∣ K * N := by
  -- 1. obtain c: def:divides, from H4
  obtain ⟨c, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := M) (n := N))).mp (by parley_side)
  -- 2. calculation
  have s2 : K * N = K * M * c := by
    calc K * N = K * (M * c) := by parley_subst s1
      _ = K * M * c := by ring
  -- 3. def:divides d := K·M, n := K·N, from 2
  have s3 : K * M ∣ K * N := ((Parley.Items.Stdlib.Divisibility.def_divides (d := K * M) (n := K * N))).mpr ⟨c, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Setmm.ScaleDivisibility.ScaleDivisibility
