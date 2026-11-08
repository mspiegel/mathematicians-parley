module

public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/size-at-least-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne

theorem size_at_least_one {α : Type*} (A : Set α) (hH2 : ¬ A = ∅) :
    ((1 : ℕ) : ℕ∞) ≤ A.encard := by
  -- 1. contradiction
  have s1 : ∃ a ∈ A, True := by
    by_contra hS
    -- 1.1. proof
    have s1_1 : ∀ s ∈ A, ¬ s ∈ A := by
      intro s hK
      intro hS2
      -- 1.1.1. exhibit, from S2
      have s1_1_1 : ∃ a ∈ A, True := ⟨s, by parley_set_side, trivial⟩
      -- 1.1.2. restate S
      have s1_1_2 : ¬ (∃ a ∈ A, True) := by parley_set_side
      exact s1_1_2 s1_1_1
    -- 1.2. calculation
    have s1_2 : A = ∅ := by
      calc A = A ∩ A := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := A)).symm
        _ = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := A) s1_1)
    -- 1.3. restate H2
    have s1_3 : ¬ A = ∅ := by parley_set_side
    exact s1_3 s1_2
  -- 2. obtain a from line 1
  obtain ⟨a, s2, _⟩ := s1
  -- 3. mun:singleton-subset, from 2
  have s3 : ({a} : Set α) ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := A) (a := a) s2)
  -- 4. mun:card-subset A := {a}, B := A, from 3
  have s4 : ((({a} : Set α).ncard : ℕ) : ℕ∞) ≤ A.encard := by (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := ({a} : Set α)) (B := A) s3); simp only [← Set.Finite.cast_ncard_eq (show ({a} : Set α).Finite by parley_finite)] at h ⊢; exact_mod_cast h)
  -- 5. substitute
  parley_count_after (by
    have c1 : (({a} : Set α).ncard : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_singleton (x := a))
    have row1 : ((1 : ℕ) : ℕ∞) ≤ A.encard := by parley_subst_at c1 s4
    exact row1)

end Parley.Proofs.Setmm.SizeAtLeastOne.SizeAtLeastOne
