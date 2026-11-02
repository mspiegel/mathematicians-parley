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
