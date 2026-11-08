module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/an-equation-the-pairs-make-true.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnEquationThePairsMakeTrue.AnEquationThePairsMakeTrue

theorem an_equation_the_pairs_make_true {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B.Finite) (hH5 : A ∩ B = ∅) :
    ((A ∪ B).ncard : ℤ) = (A.ncard : ℤ) + (B.ncard : ℤ) := by
  -- 1. mun:card-nat0 X := A, from H3
  have s1 : 0 ≤ (A.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3)
  -- 2. mun:card-nat0 X := B, from H4
  have s2 : 0 ≤ (B.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4)
  -- 3. mun:card-disjoint-union X := A, Y := B, m := |A|, n := |B|, from H5, 1, 2
  exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := (A.ncard : ℤ)) (by parley_set_side) (n := (B.ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) hH5)

end Parley.Tests.Elaborator.AnEquationThePairsMakeTrue.AnEquationThePairsMakeTrue
