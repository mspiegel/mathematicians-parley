module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/minus-one-mod.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneMod.MinusOneMod

theorem minus_one_mod (M : ℤ) (hH1 : 0 < M) :
    (-1 : ℤ) % M = M - 1 := by
  -- 1. algebra
  have s1 : -1 * M + (M - 1) = -1 := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * M + (M - 1) = -1 := ⟨(-1 : ℤ), s1⟩
  -- 3. mun:nat-minus-one n := M
  have s3 : 0 ≤ M - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := M) (by parley_side))
  -- 4. mun:mod-remainder a := −1, m := M, r := M − 1, from 2, 3
  have r19_1 : M - 1 < M := by parley_order
  exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (-1 : ℤ)) (m := M) (by parley_side) (r := M - 1) (by parley_side) r19_1)).mpr s2

end Parley.Proofs.Setmm.MinusOneMod.MinusOneMod
