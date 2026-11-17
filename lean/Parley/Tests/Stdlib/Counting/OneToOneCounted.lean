module

public import Functions
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.OneToOneCounted

theorem one_to_one_counted {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (hH3 : A.Finite) (hH4 : B.Finite) (hH5 : (A.ncard : ℤ) ≤ (B.ncard : ℤ)) :
    ({g ∈ LeanBridges.Functions.functions_from A B | Set.MapsTo g Set.univ B ∧ Set.InjOn g Set.univ}.ncard : ℤ) = (∏ j ∈ Finset.Icc (0 : ℤ) ((A.ncard : ℤ) - 1), ((B.ncard : ℤ) - j : ℤ)) := by
  -- 1. thm:count-one-to-one X := A, Y := B, from H3, H4, H5
  exact (Parley.Items.Stdlib.Counting.thm_count_one_to_one (X := A) (Y := B) hH3 hH4 hH5)

end Parley.Tests.Stdlib.Counting.OneToOneCounted
