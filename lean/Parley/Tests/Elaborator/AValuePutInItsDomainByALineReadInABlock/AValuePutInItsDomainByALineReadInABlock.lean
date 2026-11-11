module

public import Tactics
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-value-put-in-its-domain-by-a-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AValuePutInItsDomainByALineReadInABlock.AValuePutInItsDomainByALineReadInABlock

theorem a_value_put_in_its_domain_by_a_line_read_in_a_block (hH1 : ∀ x : ℤ, x ∈ Finset.Icc 1 9 → 10 - x ∈ Finset.Icc (1 : ℤ) (9 : ℤ)) (hH2 : ∀ y : ℤ, y ∈ Finset.Icc 1 9 → y ≤ 9) :
    (∀ x : ℤ, x ∈ Finset.Icc 1 9 → 10 - x ≤ 9) := by
  -- 1. proof
  intro x hK1
  try push_cast at hK1
  try have hK1_bounds := Finset.mem_Icc.mp hK1
  -- 1.1. instantiate y := 10 − x in H2, from H1
  exact (hH2 (10 - x) (hH1 x hK1))

end Parley.Tests.Elaborator.AValuePutInItsDomainByALineReadInABlock.AValuePutInItsDomainByALineReadInABlock
