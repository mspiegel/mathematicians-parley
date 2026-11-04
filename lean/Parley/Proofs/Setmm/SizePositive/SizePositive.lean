module

public import OrderTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne

/-! Written from proofs/setmm/size-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizePositive.SizePositive

theorem size_positive {α : Type*} (A : Set α) (hH2 : A.Finite) (hH3 : ¬ A = ∅) :
    0 < (A.ncard : ℤ) := by
  -- 1. thm:size-at-least-one, from H3
  have s1 : 1 ≤ (A.ncard : ℤ) := by first | linarith [(Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3)] | (have h := (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3) | (have h := (Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne.size_at_least_one (A := A) hH3); parley_set_side)
  -- 2. mun:card-nat0, from H2
  have s2 : 0 ≤ (A.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2); parley_set_side)
  -- 3. inequalities, from 1
  have s3 : 0 < (A.ncard : ℤ) := by parley_order
  all_goals exact s3

end Parley.Proofs.Setmm.SizePositive.SizePositive
