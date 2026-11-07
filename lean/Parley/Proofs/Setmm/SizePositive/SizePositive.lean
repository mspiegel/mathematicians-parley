module

public import OrderTactics
public import SetTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
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
    ((0 : ℕ) : ℕ∞) < A.encard := by
  -- 1. thm:size-at-least-one, from H3
  have s1 : ((1 : ℕ) : ℕ∞) ≤ A.encard := by first | linarith [(Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3)] | (have h := (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3) | (have h := (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3); parley_set_side)
  -- 2. mun:card-nat0, from H2
  have s2 : 0 ≤ (A.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2); parley_set_side)
  -- 3. inequalities, from 1
  have s3 : ((0 : ℕ) : ℕ∞) < A.encard := by parley_count_int; (parley_order)
  all_goals exact s3

end Parley.Proofs.Setmm.SizePositive.SizePositive
