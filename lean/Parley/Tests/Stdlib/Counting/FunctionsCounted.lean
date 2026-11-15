module

public import Functions
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FunctionsCounted

theorem functions_counted {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B.Finite) :
    (∃ m : ℕ, (LeanBridges.Functions.functions_from A B).encard = (m : ℕ∞) ∧ (m : ℤ) = (B.ncard : ℤ) ^ A.ncard) := by
  -- 1. thm:count-functions X := A, Y := B, from H3, H4
  exact (Parley.Items.Stdlib.Counting.thm_count_functions (X := A) (Y := B) hH3 hH4)

end Parley.Tests.Stdlib.Counting.FunctionsCounted
