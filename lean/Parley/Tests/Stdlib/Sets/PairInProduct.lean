module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.PairInProduct

theorem pair_in_product (a : ℝ) (b : ℝ) :
    (a, b) ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
  -- 1. mun:sets-pair-in-product
  exact ((Parley.Items.Stdlib.Sets.mun_pair_in_product (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (a := a) (b := b))).mpr ⟨Set.mem_univ _, Set.mem_univ _⟩

end Parley.Tests.Stdlib.Sets.PairInProduct
