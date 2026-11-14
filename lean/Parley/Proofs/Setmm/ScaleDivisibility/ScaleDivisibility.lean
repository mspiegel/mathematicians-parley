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

/-! Written from proofs/setmm/scale-divisibility.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ScaleDivisibility.ScaleDivisibility

theorem scale_divisibility (M : ℤ) (N : ℤ) (K : ℤ) (hH4 : M ∣ N) :
    K * M ∣ K * N := by
  -- 1. obtain c: def:divides, from H4
  obtain ⟨c, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := M) (n := N))).mp hH4
  -- 2. calculation
  have s2 : K * N = K * M * c := by
    calc K * N = K * (M * c) := congrArg (fun t : ℤ => K * t) s1
      _ = K * M * c := by ring1
  -- 3. def:divides d := K·M, n := K·N, from 2
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := K * M) (n := K * N))).mpr ⟨c, s2⟩

end Parley.Proofs.Setmm.ScaleDivisibility.ScaleDivisibility
