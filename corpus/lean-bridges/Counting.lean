module

public import Mathlib
public import Factorials

/-!
# What the page says of counting

Factorials and binomial coefficients of integers, and the counts of sets,
each item said in Lean as the build writes it. The definitions of n! and
C(n, k) are in `Factorials`. A letter the page puts in ℕ₀ is an integer with
the fact 0 ≤ n beside it; each proof takes it to Mathlib's natural numbers
with `lift`, where Mathlib's facts of n! and C(n, k) are stated.
-/

public section

namespace LeanBridges.Counting

/-- Pascal's rule for every integer k: below 0 both sides are 0, at 0 the
second coefficient is, and above 0 it is Mathlib's `Nat.choose_succ_succ'`. -/
theorem pascal (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    (choose n k : ℤ) + choose n (k - 1) = choose (n + 1) k := by
  lift n to ℕ using h1
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have h1 : ¬ (0 ≤ k - 1) := by omega
    have h2 : ¬ (0 ≤ k) := by omega
    simp only [choose, if_neg h1, if_neg h2]
    simp
  · simp [choose]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    have e1 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    have e3 : ((j : ℤ) + 1 - 1) = (j : ℤ) := by ring
    rw [e3, e1, e2, choose_natCast, choose_natCast, choose_natCast,
      Nat.choose_succ_succ']
    push_cast
    ring

/-- C(n, k) is 0 outside 0 … n. -/
theorem choose_outside (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) (h : k ∉ Finset.Icc 0 n) :
    (choose n k : ℤ) = 0 := by
  lift n to ℕ using h1
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at h
  unfold choose
  split_ifs with h0
  · lift k to ℕ using h0
    have hk : n < k := by omega
    simp [Nat.choose_eq_zero_of_lt hk]
  · simp

/-- C(n, k) is above 0 inside 0 … n. -/
theorem choose_pos (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) (h : k ∈ Finset.Icc 0 n) :
    0 < (choose n k : ℤ) := by
  lift n to ℕ using h1
  rw [Finset.mem_Icc] at h
  obtain ⟨h0, h1⟩ := h
  lift k to ℕ using h0
  rw [choose_natCast]
  exact_mod_cast Nat.choose_pos (by exact_mod_cast h1)

/-- The absorption identity, as set.mm states it. -/
theorem absorption (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) (h : k ∈ Finset.Icc 0 n) :
    (choose (n + 1) (k + 1) : ℚ) = choose n k * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by
  lift n to ℕ using h1
  rw [Finset.mem_Icc] at h
  obtain ⟨h0, _⟩ := h
  lift k to ℕ using h0
  have e1 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, choose_natCast, choose_natCast]
  have key : ((n + 1 : ℕ) : ℚ) * (n.choose k : ℚ) =
      ((n + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  push_cast at key ⊢
  field_simp
  linarith

end LeanBridges.Counting

namespace LeanBridges.Counting

/-- `def:stdlib/counting/factorial`, its sentence 1. -/
theorem factorial_1 :
    (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 :=
  by simp

/-- `def:stdlib/counting/factorial`, its sentence 2. -/
theorem factorial_2 :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 :=
  by simp

/-- `def:stdlib/counting/factorial`, its sentence 3. -/
theorem factorial_3 (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial (n + 1) : ℤ) = (LeanBridges.Counting.factorial n : ℤ) * (n + 1) := by
  lift n to ℕ using h1
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, LeanBridges.Counting.factorial_natCast, LeanBridges.Counting.factorial_natCast, Nat.factorial_succ]; push_cast; ring

/-- `mun:stdlib/counting/factorial-nat`. -/
theorem factorial_nat (n : ℤ) (h1 : 0 ≤ n) :
    0 < (LeanBridges.Counting.factorial n : ℤ) := by
  lift n to ℕ using h1
  simpa using Nat.factorial_pos n

/-- `mun:stdlib/counting/factorial-at-most`. -/
theorem factorial_at_most (m : ℤ) (h1 : 0 ≤ m) (n : ℤ) (h2 : 0 ≤ n) (h3 : m ≤ n) :
    (LeanBridges.Counting.factorial m : ℤ) ≤ (LeanBridges.Counting.factorial n : ℤ) := by
  lift m to ℕ using h1
  lift n to ℕ using h2
  simpa using Nat.factorial_le (show m ≤ n by exact_mod_cast h3)

/-- `mun:stdlib/counting/factorial-divisible`. -/
theorem factorial_divisible (n : ℤ) (h1 : 0 < n) (m : ℤ) (h2 : 0 < m) (h3 : m ≤ n) :
    m ∣ (LeanBridges.Counting.factorial n : ℤ) := by
  lift n to ℕ using h1.le
  lift m to ℕ using h2.le
  simpa using Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial (by exact_mod_cast h2) (show m ≤ n by exact_mod_cast h3))

/-- `def:stdlib/counting/C`, its sentence 1. -/
theorem C_1 (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (-1 : ℤ) : ℤ) = 0 :=
  by simp [LeanBridges.Counting.choose]

/-- `def:stdlib/counting/C`, its sentence 2. -/
theorem C_2 (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    k ∈ Finset.Icc (0 : ℤ) n → (LeanBridges.Counting.choose n k : ℚ) = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) := by
  lift n to ℕ using h1
  intro h; obtain ⟨h0, h1⟩ := Finset.mem_Icc.mp h; lift k to ℕ using h0; have hk : k ≤ n := (by exact_mod_cast h1); rw [show (n : ℤ) - (k : ℤ) = ((n - k : ℕ) : ℤ) from (Nat.cast_sub hk).symm]; simp only [LeanBridges.Counting.choose_natCast, LeanBridges.Counting.factorial_natCast]; rw [Nat.cast_choose ℚ hk, mul_comm]

/-- `def:stdlib/counting/C`, its sentence 3. -/
theorem C_3 (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    n < k → (LeanBridges.Counting.choose n k : ℤ) = 0 := by
  lift n to ℕ using h1
  intro h; have h0 : (0 : ℤ) ≤ k := (by omega); lift k to ℕ using h0; have hk : n < k := (by exact_mod_cast h); simp [Nat.choose_eq_zero_of_lt hk]

/-- `mun:stdlib/counting/binomial-zero-index`. -/
theorem binomial_zero_index (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (0 : ℤ) : ℤ) = 1 := by
  lift n to ℕ using h1
  simp [LeanBridges.Counting.choose]

/-- `mun:stdlib/counting/binomial-one`. -/
theorem binomial_one (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n := by
  lift n to ℕ using h1
  simp [LeanBridges.Counting.choose]

/-- `mun:stdlib/counting/binomial-all`. -/
theorem binomial_all (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n n : ℤ) = 1 := by
  lift n to ℕ using h1
  simp

/-- `mun:stdlib/counting/binomial-two`. -/
theorem binomial_two (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  lift n to ℕ using h1
  simp [LeanBridges.Counting.choose, Nat.cast_choose_two]

/-- `mun:stdlib/counting/binomial-nat0`. -/
theorem binomial_nat0 (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    0 ≤ (LeanBridges.Counting.choose n k : ℤ) :=
  by positivity

/-- `mun:stdlib/counting/factorial-nonzero`. -/
theorem factorial_nonzero (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial n : ℤ) ≠ 0 := by
  lift n to ℕ using h1
  simp [Nat.factorial_ne_zero]

end LeanBridges.Counting

namespace LeanBridges.Counting

/-- `mun:stdlib/counting/card-singleton`. -/
theorem card_singleton {α : Type*} (x : α) :
    ({x} : Set α).encard = ((1 : ℕ) : ℕ∞) :=
  by simp

/-- `mun:stdlib/counting/card-disjoint-union`. -/
theorem card_disjoint_union {α : Type*} (X : Set α) (Y : Set α) (m : ℤ) (h1 : 0 ≤ m) (n : ℤ) (h2 : 0 ≤ n)
    (h3 : X.encard = ((m.toNat : ℕ) : ℕ∞)) (h4 : Y.encard = ((n.toNat : ℕ) : ℕ∞)) (h5 : X ∩ Y = ∅) :
    (X ∪ Y).encard = (((m + n).toNat : ℕ) : ℕ∞) := by
  rw [Int.toNat_add h1 h2, Set.encard_union_eq (Set.disjoint_iff_inter_eq_empty.mpr h5), h3, h4]; push_cast; rfl

/-- `mun:stdlib/counting/card-empty`. -/
theorem card_empty {α : Type*} :
    (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) :=
  by simp

/-- `mun:stdlib/counting/card-at-least-one`. -/
theorem card_at_least_one {α : Type*} (X : Set α) (h1 : ¬ X = ∅) :
    ((1 : ℕ) : ℕ∞) ≤ X.encard :=
  by simpa using Set.one_le_encard_iff_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr h1)

/-- `mun:stdlib/counting/card-pair`. -/
theorem card_pair {α : Type*} (u : α) (w : α) :
    ({u, w} : Set α).encard ≤ ((2 : ℕ) : ℕ∞) := by
  by_cases h : u = w
  · subst h; simp
  · rw [Set.encard_pair h]; rfl

/-- `mun:stdlib/counting/card-pair-distinct`. -/
theorem card_pair_distinct {α : Type*} (u : α) (w : α) :
    ¬ u = w ↔ ({u, w} : Set α).encard = ((2 : ℕ) : ℕ∞) :=
  ⟨fun h => by rw [Set.encard_pair h]; rfl, fun h hu => by subst hu; simp at h⟩

/-- `mun:stdlib/counting/card-two`. -/
theorem card_two {α : Type*} (Y : Set α) (a : α) (b : α) (h1 : Y.encard = ((2 : ℕ) : ℕ∞)) (h2 : a ∈ Y) (h3 : b ∈ Y) (h4 : ¬ a = b) :
    Y = ({a, b} : Set α) :=
  (Set.Finite.eq_of_subset_of_encard_le (s := ({a, b} : Set α)) (t := Y) (Set.toFinite _) (Set.insert_subset_iff.mpr ⟨h2, Set.singleton_subset_iff.mpr h3⟩) (by simp [h1, Set.encard_pair h4])).symm

/-- `mun:stdlib/counting/card-positive`. -/
theorem card_positive {α : Type*} (X : Set α) (h1 : ((0 : ℕ) : ℕ∞) < X.encard) :
    ¬ X = ∅ :=
  by intro h; subst h; simp at h1

end LeanBridges.Counting
