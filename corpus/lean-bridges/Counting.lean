module

public import Mathlib

/-!
# Factorials and binomial coefficients as the page reads them

The page writes n! and C(n, k) of integers: (n − k)! inside the formula for
C(n, k), and C(n, k − 1) in Pascal's rule. Mathlib's `Nat.factorial` and
`Nat.choose` take naturals, and a natural subtraction stops at 0, so each is
taken here of integers and is Mathlib's on the naturals.

- n! is `Nat.factorial` of n's `toNat`. The page writes it only where n is
  not negative.
- C(n, k) is set.mm's: `Nat.choose` where k is not negative, which is
  already 0 above n, and 0 where k is negative.
-/

public section

namespace LeanBridges.Counting

/-- n! of an integer n that is not negative: `Nat.factorial n.toNat`. -/
@[expose] def factorial (n : ℤ) : ℕ :=
  n.toNat.factorial

/-- C(n, k): `Nat.choose n k` for k ≥ 0, and 0 for k < 0. -/
@[expose] def choose (n k : ℤ) : ℕ :=
  if 0 ≤ k then Nat.choose n.toNat k.toNat else 0

/-- A natural's factorial is Mathlib's. -/
@[simp] theorem factorial_natCast (n : ℕ) : factorial n = n.factorial := by
  simp [factorial]

/-- A numeral's factorial is Mathlib's, so that `norm_num` works it out. -/
@[simp] theorem factorial_ofNat (n : ℕ) [n.AtLeastTwo] :
    factorial (no_index (OfNat.ofNat n : ℤ)) = (OfNat.ofNat n : ℕ).factorial := rfl

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl

@[simp] theorem factorial_one : factorial 1 = 1 := rfl

/-- A coefficient of naturals is Mathlib's. -/
@[simp] theorem choose_natCast (n k : ℕ) : choose n k = n.choose k := by
  simp [choose]

/-- Pascal's rule for every integer k: below 0 both sides are 0, at 0 the
second coefficient is, and above 0 it is Mathlib's `Nat.choose_succ_succ'`. -/
theorem pascal (n : ℕ) (k : ℤ) :
    (choose n k : ℤ) + choose n (k - 1) = choose ((n : ℤ) + 1) k := by
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
theorem choose_outside (n : ℕ) (k : ℤ) (h : k ∉ Finset.Icc 0 (n : ℤ)) :
    (choose n k : ℤ) = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at h
  unfold choose
  split_ifs with h0
  · lift k to ℕ using h0
    have hk : n < k := by omega
    simp [Nat.choose_eq_zero_of_lt hk]
  · simp

/-- C(n, k) is above 0 inside 0 … n. -/
theorem choose_pos (n : ℕ) (k : ℤ) (h : k ∈ Finset.Icc 0 (n : ℤ)) :
    0 < (choose n k : ℤ) := by
  rw [Finset.mem_Icc] at h
  obtain ⟨h0, h1⟩ := h
  lift k to ℕ using h0
  rw [choose_natCast]
  exact_mod_cast Nat.choose_pos (by exact_mod_cast h1)

/-- The absorption identity, as set.mm states it. -/
theorem absorption (n : ℕ) (k : ℤ) (h : k ∈ Finset.Icc 0 (n : ℤ)) :
    (choose ((n : ℤ) + 1) (k + 1) : ℚ) = choose n k * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by
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
theorem factorial_3 (n : ℕ) :
    (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) :=
  by rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, LeanBridges.Counting.factorial_natCast, LeanBridges.Counting.factorial_natCast, Nat.factorial_succ]; push_cast; ring

/-- `mun:stdlib/counting/factorial-nat`. -/
theorem factorial_nat (n : ℕ) :
    0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  by simpa using Nat.factorial_pos n

/-- `mun:stdlib/counting/factorial-at-most`. -/
theorem factorial_at_most (m : ℕ) (n : ℕ) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (LeanBridges.Counting.factorial (m : ℤ) : ℤ) ≤ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  by simpa using Nat.factorial_le (show m ≤ n by exact_mod_cast h3)

/-- `mun:stdlib/counting/factorial-divisible`. -/
theorem factorial_divisible (n : ℕ) (h1 : 0 < n) (m : ℕ) (h2 : 0 < m) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (m : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  by simpa using Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial h2 (show m ≤ n by exact_mod_cast h3))

/-- `def:stdlib/counting/C`, its sentence 1. -/
theorem C_1 (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (-1 : ℤ) : ℤ) = 0 :=
  by simp [LeanBridges.Counting.choose]

/-- `def:stdlib/counting/C`, its sentence 2. -/
theorem C_2 (n : ℕ) (k : ℤ) :
    k ∈ Finset.Icc (0 : ℤ) (n : ℤ) → (LeanBridges.Counting.choose (n : ℤ) k : ℚ) = (LeanBridges.Counting.factorial (n : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((n : ℤ) - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) :=
  by intro h; obtain ⟨h0, h1⟩ := Finset.mem_Icc.mp h; lift k to ℕ using h0; have hk : k ≤ n := (by exact_mod_cast h1); rw [show (n : ℤ) - (k : ℤ) = ((n - k : ℕ) : ℤ) from (Nat.cast_sub hk).symm]; simp only [LeanBridges.Counting.choose_natCast, LeanBridges.Counting.factorial_natCast]; rw [Nat.cast_choose ℚ hk, mul_comm]

/-- `def:stdlib/counting/C`, its sentence 3. -/
theorem C_3 (n : ℕ) (k : ℤ) :
    (n : ℤ) < k → (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  by intro h; have h0 : (0 : ℤ) ≤ k := (by omega); lift k to ℕ using h0; have hk : n < k := (by exact_mod_cast h); simp [Nat.choose_eq_zero_of_lt hk]

/-- `mun:stdlib/counting/binomial-zero-index`. -/
theorem binomial_zero_index (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (0 : ℤ) : ℤ) = 1 :=
  by simp [LeanBridges.Counting.choose]

/-- `mun:stdlib/counting/binomial-one`. -/
theorem binomial_one (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) :=
  by simp [LeanBridges.Counting.choose]

/-- `mun:stdlib/counting/binomial-all`. -/
theorem binomial_all (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (n : ℤ) : ℤ) = 1 :=
  by simp

/-- `mun:stdlib/counting/binomial-two`. -/
theorem binomial_two (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
  by simp [LeanBridges.Counting.choose, Nat.cast_choose_two]

/-- `mun:stdlib/counting/binomial-nat0`. -/
theorem binomial_nat0 (n : ℕ) (k : ℤ) :
    0 ≤ (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  by positivity

/-- `mun:stdlib/counting/factorial-nonzero`. -/
theorem factorial_nonzero (n : ℕ) :
    (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 :=
  by simp [Nat.factorial_ne_zero]

end LeanBridges.Counting

namespace LeanBridges.Counting

/-- `mun:stdlib/counting/card-singleton`. -/
theorem card_singleton {α : Type*} (x : α) :
    ({x} : Set α).encard = ((1 : ℕ) : ℕ∞) :=
  by simp

/-- `mun:stdlib/counting/card-disjoint-union`. -/
theorem card_disjoint_union {α : Type*} (X : Set α) (Y : Set α) (m : ℕ) (n : ℕ) (h3 : X.encard = ((m : ℕ) : ℕ∞)) (h4 : Y.encard = ((n : ℕ) : ℕ∞)) (h5 : X ∩ Y = ∅) :
    (X ∪ Y).encard = ((m + n : ℕ) : ℕ∞) :=
  by rw [Set.encard_union_eq (Set.disjoint_iff_inter_eq_empty.mpr h5), h3, h4]; push_cast; rfl

/-- `mun:stdlib/counting/card-empty`. -/
theorem card_empty {α : Type*} :
    (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) :=
  by simp

/-- `mun:stdlib/counting/card-nat0`. -/
theorem card_nat0 {α : Type*} (X : Set α) (h1 : X.Finite) :
    ∃ m : ℕ, (m : ℕ∞) = X.encard :=
  ⟨X.ncard, h1.cast_ncard_eq⟩

/-- `mun:stdlib/counting/card-at-least-one`. -/
theorem card_at_least_one {α : Type*} (X : Set α) (h1 : ¬ X = ∅) :
    ((1 : ℕ) : ℕ∞) ≤ X.encard :=
  by simpa using Set.one_le_encard_iff_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr h1)

/-- `mun:stdlib/counting/card-pair`. -/
theorem card_pair {α : Type*} (u : α) (w : α) :
    ({u, w} : Set α).encard ≤ ((2 : ℕ) : ℕ∞) :=
  by rcases eq_or_ne u w with h | h <;> first | (subst h; simp; done) | (rw [Set.encard_pair h]; rfl)

/-- `mun:stdlib/counting/card-pair-distinct`. -/
theorem card_pair_distinct {α : Type*} (u : α) (w : α) :
    ¬ u = w ↔ ({u, w} : Set α).encard = ((2 : ℕ) : ℕ∞) :=
  ⟨fun h => by simpa using Set.encard_pair h, fun h hu => by subst hu; simp at h⟩

/-- `mun:stdlib/counting/card-two`. -/
theorem card_two {α : Type*} (Y : Set α) (a : α) (b : α) (h1 : Y.encard = ((2 : ℕ) : ℕ∞)) (h2 : a ∈ Y) (h3 : b ∈ Y) (h4 : ¬ a = b) :
    Y = ({a, b} : Set α) :=
  (Set.Finite.eq_of_subset_of_encard_le (s := ({a, b} : Set α)) (t := Y) (Set.toFinite _) (Set.insert_subset_iff.mpr ⟨h2, Set.singleton_subset_iff.mpr h3⟩) (by simp [h1, Set.encard_pair h4])).symm

/-- `mun:stdlib/counting/card-positive`. -/
theorem card_positive {α : Type*} (X : Set α) (h1 : ((0 : ℕ) : ℕ∞) < X.encard) :
    ¬ X = ∅ :=
  by intro h; subst h; simp at h1

end LeanBridges.Counting
