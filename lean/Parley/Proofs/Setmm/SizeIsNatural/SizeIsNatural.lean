module

public import ArithTactics
public import SetTactics
public import SubstTactics
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

/-! Written from proofs/setmm/size-is-natural.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeIsNatural.SizeIsNatural

theorem size_is_natural {α : Type*} (A : Set α) (hH2 : A.Finite) :
    (0 < (A.ncard : ℤ) ↔ ¬ A = ∅) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hC1
    intro hS1
    -- 1. calculation
    have s1 : (A.ncard : ℤ) = 0 := by parley_count_after (by
      calc (A.ncard : ℤ) = ((∅ : Set α).ncard : ℤ) := by parley_subst hS1
        _ = 0 := by exact Parley.Items.Stdlib.Counting.mun_card_empty)
    -- 2. arithmetic
    have s2 : ¬ (0 : ℤ) < 0 := by parley_arith
    -- 3. substitute |A| = 0 (line 1) into line 2
    have s3 : ¬ 0 < (A.ncard : ℤ) := by parley_count_int; ((have h := Eq.subst (motive := (fun t : ℤ => ¬ 0 < t)) s1.symm s2; push_cast at h ⊢; all_goals exact_mod_cast h))
    exact s3 hC1
  · skip
    intro hC2
    -- 4. mun:card-nat0, from H2
    have s4 : 0 ≤ (A.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH2)
    -- 5. contradiction
    have s5 : (A.ncard : ℤ) ≠ 0 := by
      intro hS2
      -- 5.1. mun:card-zero X := A, from S2
      have s5_1 : A = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := A) (by parley_set_side))
      -- 5.2. restate C2
      have s5_2 : ¬ A = ∅ := by exact hC2
      exact s5_2 s5_1
    -- 6. mun:nat0-nonzero m := |A|, from 4, 5
    exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (A.ncard : ℤ)) (by parley_set_side) (by parley_set_side))

end Parley.Proofs.Setmm.SizeIsNatural.SizeIsNatural
