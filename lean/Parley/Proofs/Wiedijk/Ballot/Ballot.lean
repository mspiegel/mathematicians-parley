module

public import Counting
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.BallotCount
public import Parley.Proofs.Wiedijk.Ballot.GoodFinite
public import Parley.Proofs.Wiedijk.Combinations.Combinations

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.Ballot

theorem ballot (m : ℤ) (hH1 : 0 < m) (n : ℤ) (hH2 : 0 < n) (hH3 : n < m) :
    ({a ∈ {c ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (c.ncard : ℤ) = m} | ∀ b : ℤ, b ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) b : Set ℤ) \ a).ncard : ℤ) < (((Set.Icc (1 : ℤ) b : Set ℤ) ∩ a).ncard : ℤ)}.ncard : ℚ) / ({a ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (a.ncard : ℤ) = m}.ncard : ℚ) = ((m : ℚ) - (n : ℚ)) / ((m : ℚ) + (n : ℚ)) := by
  set O : Set (Set ℤ) := {c ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (c.ncard : ℤ) = m} with hD3
  have hD3_finite : O.Finite := by rw [hD3]; exact ((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)
  set E : Set (Set ℤ) := {c ∈ O | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} with hD4
  have hD4_finite : E.Finite := by rw [hD4]; exact (hD3_finite).subset (fun _ h => h.1)
  -- 1. thm:ballot-count a := m, b := n, from D3, D4
  have r1152_1 : n ≤ m := by linarith only [hH3]
  have s1 : (E.ncard : ℤ) * (m + n) = (m - n) * (LeanBridges.Counting.choose (m + n) m : ℤ) := by
    simp only [hD3, hD4] at ⊢
    push_cast at ⊢
    exact (Parley.Proofs.Wiedijk.Ballot.BallotCount.ballot_count (a := m) (le_of_lt hH1) (b := n) (le_of_lt hH2) r1152_1)
  -- 2. thm:good-finite, from D3, D4
  have s2 : E.Finite := by
    simp only [hD3, hD4] at ⊢
    push_cast at ⊢
    exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (le_of_lt hH1) (n := n) (le_of_lt hH2))
  -- 3. mun:card-nat0 X := E, from 2
  have s3 : 0 ≤ (E.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := E) s2)
  -- 4. mun:range-size n := m + n
  have s4 : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ).ncard : ℤ) = m + n := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (add_nonneg (le_of_lt hH1) (le_of_lt hH2)))
  -- 5. thm:combinations n := m + n, k := m, A := {1, …, m + n}, from D3, 4
  have s5 : (O.ncard : ℤ) = (LeanBridges.Counting.choose (m + n) m : ℤ) := by
    simp only [hD3] at ⊢
    push_cast at ⊢
    exact (Parley.Proofs.Wiedijk.Combinations.Combinations.combinations (A := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (n := m + n) (add_nonneg (le_of_lt hH1) (le_of_lt hH2)) (k := m) (by (have h := congrArg Int.toNat (s4); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s4; rw [h0] at h; exact ne_of_lt ((add_pos (hH1) (hH2) : 0 < m + n)) (by exact_mod_cast h)) : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) : Set ℤ).Finite)), h])))
  -- 6. inequalities, from H2
  have s6 : m ≤ m + n := by linarith only [hH2]
  -- 7. mun:binomial-nat n := m + n, k := m
  have r1171_1 : m ∈ Finset.Icc (0 : ℤ) (m + n) := ((Parley.Items.Stdlib.Sums.def_range0 (k := m) (n := m + n) (add_nonneg (le_of_lt hH1) (le_of_lt hH2)))).mpr ⟨le_of_lt hH1, s6⟩
  have s7 : 0 < (LeanBridges.Counting.choose (m + n) m : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat (n := m + n) (add_nonneg (le_of_lt hH1) (le_of_lt hH2)) (k := m) r1171_1)
  -- 8. substitute |O| = C(m + n, m) (line 5) into line 7
  have s8 : 0 < (O.ncard : ℤ) := Eq.subst (motive := (fun t : ℤ => 0 < t)) s5.symm s7
  -- 9. algebra, from 1, 3, 5
  have r1178_1 : (O.ncard : ℤ) ≠ 0 := by exact s8.ne'
  have s1_w : (E.ncard : ℚ) * ((m : ℚ) + (n : ℚ)) = ((m : ℚ) - (n : ℚ)) * (LeanBridges.Counting.choose (m + n) m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h ⊢; linear_combination h
  have s5_w : (O.ncard : ℚ) = (LeanBridges.Counting.choose (m + n) m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s5; push_cast at h ⊢; linear_combination h
  have hz1 : (O.ncard : ℚ) ≠ 0 := (by exact_mod_cast r1178_1); have hz2 : (m : ℚ) + (n : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((1) / (((O.ncard : ℚ)) * ((m : ℚ) + (n : ℚ)))) * s1_w + ((-(m : ℚ) + (n : ℚ)) / (((O.ncard : ℚ)) * ((m : ℚ) + (n : ℚ)))) * s5_w

end Parley.Proofs.Wiedijk.Ballot.Ballot
