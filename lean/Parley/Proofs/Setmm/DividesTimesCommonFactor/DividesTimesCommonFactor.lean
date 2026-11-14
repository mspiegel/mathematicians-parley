module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/divides-times-common-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DividesTimesCommonFactor.DividesTimesCommonFactor

theorem divides_times_common_factor (M : ℤ) (N : ℤ) (K : ℤ) (hH4 : M ∣ N) :
    M * K ∣ N * K := by
  -- 1. obtain j: def:divides d := M, n := N, from H4
  obtain ⟨j, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := M) (n := N))).mp hH4
  -- 2. calculation
  have s2 : N * K = M * K * j := by
    calc N * K = M * j * K := congrArg (fun t : ℤ => t * K) s1
      _ = M * K * j := by ring1
  -- 3. def:divides d := M·K, n := N·K, from 2
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := M * K) (n := N * K))).mpr ⟨j, s2⟩

end Parley.Proofs.Setmm.DividesTimesCommonFactor.DividesTimesCommonFactor
