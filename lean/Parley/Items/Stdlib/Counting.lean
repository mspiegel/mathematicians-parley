module

public import Counting
public import Tactics

/-! Written from corpus/stdlib/counting.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Counting

theorem def_factorial_1 :
    (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.factorial_1

theorem def_factorial_2 :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.factorial_2

theorem def_factorial_3 (n : ℕ) :
    (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) :=
  LeanBridges.Counting.factorial_3 n

theorem mun_factorial_nat (n : ℕ) :
    0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  LeanBridges.Counting.factorial_nat n

theorem mun_factorial_at_most (m : ℕ) (n : ℕ) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (LeanBridges.Counting.factorial (m : ℤ) : ℤ) ≤ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  LeanBridges.Counting.factorial_at_most m n h3

theorem mun_factorial_divisible (n : ℕ) (h1 : 0 < n) (m : ℕ) (h2 : 0 < m) (h3 : (m : ℤ) ≤ (n : ℤ)) :
    (m : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) :=
  LeanBridges.Counting.factorial_divisible n h1 m h2 h3

theorem mun_card_zero {α : Type*} (X : Set α) (h1 : X.encard = ((0 : ℕ) : ℕ∞)) :
    X = ∅ :=
  Set.encard_eq_zero.mp (by simpa using h1)

theorem mun_card_singleton {α : Type*} (x : α) :
    ({x} : Set α).encard = ((1 : ℕ) : ℕ∞) :=
  LeanBridges.Counting.card_singleton x

theorem mun_card_disjoint_union {α : Type*} (X : Set α) (Y : Set α) (m : ℕ) (n : ℕ) (h3 : X.encard = ((m : ℕ) : ℕ∞)) (h4 : Y.encard = ((n : ℕ) : ℕ∞)) (h5 : X ∩ Y = ∅) :
    (X ∪ Y).encard = ((m + n : ℕ) : ℕ∞) :=
  LeanBridges.Counting.card_disjoint_union X Y m n h3 h4 h5

theorem def_C_1 (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (-1 : ℤ) : ℤ) = 0 :=
  LeanBridges.Counting.C_1 n

theorem def_C_2 (n : ℕ) (k : ℤ) :
    k ∈ Finset.Icc (0 : ℤ) (n : ℤ) → (LeanBridges.Counting.choose (n : ℤ) k : ℚ) = (LeanBridges.Counting.factorial (n : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((n : ℤ) - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) :=
  LeanBridges.Counting.C_2 n k

theorem def_C_3 (n : ℕ) (k : ℤ) :
    (n : ℤ) < k → (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  LeanBridges.Counting.C_3 n k

theorem thm_pascal (n : ℕ) (k : ℤ) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (k - 1) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) k : ℤ) :=
  LeanBridges.Counting.pascal n k

theorem thm_absorption (n : ℕ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) :=
  LeanBridges.Counting.absorption n k h2

theorem mun_binomial_zero_index (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (0 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.binomial_zero_index n

theorem mun_binomial_one (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) :=
  LeanBridges.Counting.binomial_one n

theorem mun_binomial_all (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (n : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.binomial_all n

theorem mun_binomial_two (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
  LeanBridges.Counting.binomial_two n

theorem mun_binomial_outside (n : ℕ) (k : ℤ) (h3 : ¬ k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℤ) = 0 :=
  LeanBridges.Counting.choose_outside n k h3

theorem mun_binomial_nat0 (n : ℕ) (k : ℤ) :
    0 ≤ (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  LeanBridges.Counting.binomial_nat0 n k

theorem mun_binomial_nat (n : ℕ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    0 < (LeanBridges.Counting.choose (n : ℤ) k : ℤ) :=
  LeanBridges.Counting.choose_pos n k h2

theorem mun_card_empty {α : Type*} :
    (∅ : Set α).encard = ((0 : ℕ) : ℕ∞) :=
  LeanBridges.Counting.card_empty

theorem mun_finite_part {α : Type*} (X : Set α) (Y : Set α) (h1 : X.Finite) (h2 : Y ⊆ X) :
    Y.Finite :=
  h1.subset h2

theorem mun_factorial_nonzero (n : ℕ) :
    (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 :=
  LeanBridges.Counting.factorial_nonzero n

theorem mun_card_nat0 {α : Type*} (X : Set α) (h1 : X.Finite) :
    ∃ m : ℕ, (m : ℕ∞) = X.encard :=
  LeanBridges.Counting.card_nat0 X h1

theorem mun_card_finite {α : Type*} (X : Set α) (m : ℕ) (h2 : X.encard = ((m : ℕ) : ℕ∞)) :
    X.Finite :=
  Set.finite_of_encard_eq_coe h2

theorem mun_card_at_least_one {α : Type*} (X : Set α) (h1 : ¬ X = ∅) :
    ((1 : ℕ) : ℕ∞) ≤ X.encard :=
  LeanBridges.Counting.card_at_least_one X h1

theorem mun_card_pair {α : Type*} (u : α) (w : α) :
    ({u, w} : Set α).encard ≤ ((2 : ℕ) : ℕ∞) :=
  LeanBridges.Counting.card_pair u w

theorem mun_card_subset {α : Type*} (A : Set α) (B : Set α) (h1 : A ⊆ B) :
    A.encard ≤ B.encard :=
  Set.encard_le_encard h1

theorem mun_card_pair_distinct {α : Type*} (u : α) (w : α) :
    ¬ u = w ↔ ({u, w} : Set α).encard = ((2 : ℕ) : ℕ∞) :=
  LeanBridges.Counting.card_pair_distinct u w

theorem mun_card_two {α : Type*} (Y : Set α) (a : α) (b : α) (h1 : Y.encard = ((2 : ℕ) : ℕ∞)) (h2 : a ∈ Y) (h3 : b ∈ Y) (h4 : ¬ a = b) :
    Y = ({a, b} : Set α) :=
  LeanBridges.Counting.card_two Y a b h1 h2 h3 h4

theorem mun_card_positive {α : Type*} (X : Set α) (h1 : ((0 : ℕ) : ℕ∞) < X.encard) :
    ¬ X = ∅ :=
  LeanBridges.Counting.card_positive X h1

end Parley.Items.Stdlib.Counting
