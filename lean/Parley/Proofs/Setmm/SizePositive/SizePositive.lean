module

public import OrderTactics
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
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne

/-! Written from proofs/setmm/size-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizePositive.SizePositive

theorem size_positive {α : Type*} (A : Set α) (hH2 : A.Finite) (hH3 : ¬ A = ∅) :
    0 < (A.ncard : ℤ) := by
  -- 1. thm:size-at-least-one, from H3
  have s1 : 1 ≤ (A.ncard : ℤ) := by (have h := (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3); simp only [← Set.Finite.cast_ncard_eq ((hH2 : (A : Set α).Finite))] at h ⊢; exact_mod_cast h)
  -- 2. mun:card-nat0, from H2
  have s2 : 0 ≤ (A.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2)
  -- 3. inequalities, from 1
  parley_count_int; (parley_order)

end Parley.Proofs.Setmm.SizePositive.SizePositive
