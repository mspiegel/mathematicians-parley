module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/divides-times-common-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DividesTimesCommonFactor.DividesTimesCommonFactor

theorem divides_times_common_factor (M : ℤ) (N : ℤ) (K : ℤ) (hH4 : M ∣ N) :
    M * K ∣ N * K := by
  -- 1. obtain j: def:divides d := M, n := N, from H4
  obtain ⟨j, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := M) (n := N))).mp (by parley_side)
  -- 2. calculation
  have s2 : N * K = M * K * j := by
    calc N * K = M * j * K := by parley_subst s1
      _ = M * K * j := by parley_ring
  -- 3. def:divides d := M·K, n := N·K, from 2
  have s3 : M * K ∣ N * K := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := M * K) (n := N * K))).mpr ⟨j, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := M * K) (n := N * K))).mpr ⟨j, by parley_side⟩; parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.DividesTimesCommonFactor.DividesTimesCommonFactor
