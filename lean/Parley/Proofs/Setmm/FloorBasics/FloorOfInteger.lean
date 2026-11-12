module

public import Tactics
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorOfInteger

theorem floor_of_integer (A : ℤ) :
    ⌊(A : ℝ)⌋ = A := by
  -- 1. inequalities
  have s1 : A ≤ A := by linarith only []
  -- 2. inequalities
  have s2 : A < A + 1 := by linarith only []
  -- 3. mun:floor-between x := A, k := A, from 1, 2
  exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ)) (k := A))).mpr ⟨by exact_mod_cast s1, by exact_mod_cast s2⟩

end Parley.Proofs.Setmm.FloorBasics.FloorOfInteger
