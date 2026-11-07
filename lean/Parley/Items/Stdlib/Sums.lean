module

public import Sums
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Int
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar

/-! Written from corpus/stdlib/sums.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sums

theorem mun_sum_divisible (t : ℤ → ℤ) (n : ℤ) (h1 : 0 ≤ n) (m : ℤ) (h3 : ∀ k : ℤ, 0 ≤ k → m ∣ t k) :
    m ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : ℤ)) :=
  by apply Finset.dvd_sum; intro k hk; rw [Finset.mem_Icc] at hk; exact h3 k hk.1

theorem mun_sum_integer (t : ℤ → ℤ) (n : ℤ) (h1 : 0 ≤ n) :
    True :=
  by simp_all

theorem mun_sum_difference (t : ℤ → ℤ) (u : ℤ → ℤ) (n : ℤ) (h1 : 0 ≤ n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k - u k : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : ℤ)) - (∑ k ∈ Finset.Icc (0 : ℤ) n, (u k : ℤ)) :=
  by simp_all

theorem mun_sum_single {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) :
    (∑ k ∈ Finset.Icc a a, (t k : K)) = t a :=
  LeanBridges.Sums.sum_single t a

theorem mun_sum_last {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (n : ℤ) (h1 : 0 ≤ n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n + 1), (t k : K)) = (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : K)) + t (n + 1) :=
  LeanBridges.Sums.sum_last t n h1

theorem mun_sum_extended {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (n : ℤ) (h3 : a ≤ n) :
    (∑ k ∈ Finset.Icc a (n + 1), (t k : K)) = (∑ k ∈ Finset.Icc a n, (t k : K)) + t (n + 1) :=
  LeanBridges.Sums.sum_extended t a n h3

theorem thm_sum_telescopes {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : a ≤ b + 1) :
    (∑ k ∈ Finset.Icc a b, (t k - t (k + 1) : K)) = t a - t (b + 1) :=
  by obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a - 1 + n := ⟨(b - (a - 1)).toNat, by omega⟩; subst hn; clear h3; induction n with | zero => (simp only [Nat.cast_zero, add_zero]; rw [Finset.Icc_eq_empty_of_lt (by omega)]; simp) | succ k ih => (rw [(show a - 1 + ((k + 1 : ℕ) : ℤ) = (a - 1 + k) + 1 by push_cast; ring), (show Finset.Icc a (a - 1 + k + 1) = insert (a - 1 + k + 1) (Finset.Icc a (a - 1 + k)) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega), Finset.sum_insert (by simp), ih]; ring)

theorem thm_sum_telescopes_up {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : a ≤ b + 1) :
    (∑ k ∈ Finset.Icc a b, (t (k + 1) - t k : K)) = t (b + 1) - t a :=
  by have key : ∀ n : ℕ, ∑ k ∈ Finset.Icc a (a - 1 + n), (t (k + 1) - t k) = t (a - 1 + n + 1) - t a := (by intro n; induction n with | zero => (rw [Nat.cast_zero, add_zero, Finset.Icc_eq_empty_of_lt (by omega)]; simp) | succ n ih => (rw [(show a - 1 + ((n + 1 : ℕ) : ℤ) = (a - 1 + n) + 1 by push_cast; ring), ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert (by simp), ih]; ring)); have := key (b + 1 - a).toNat; rwa [(show a - 1 + ((b + 1 - a).toNat : ℤ) = b by omega)] at this

theorem mun_sum_first {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (n : ℤ) (h1 : 0 ≤ n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : K)) = t 0 + (∑ k ∈ Finset.Icc (0 + 1 : ℤ) n, (t k : K)) :=
  LeanBridges.Sums.sum_first t n h1

theorem mun_sum_shift {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : ℤ) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc (a + c) (b + c), (t (k - c) : K)) :=
  LeanBridges.Sums.sum_shift t a b c

theorem mun_sum_scaled {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : K) :
    c * (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc a b, (c * t k : K)) :=
  Finset.mul_sum _ _ _

theorem mun_sum_add {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) :
    (∑ k ∈ Finset.Icc a b, (t k + u k : K)) = (∑ k ∈ Finset.Icc a b, (t k : K)) + (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_add_distrib

theorem mun_sum_termwise {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_congr rfl h3

theorem mun_sum_termwise_complex {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_congr rfl h3

theorem mun_sum_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_product_real {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) :
    True :=
  trivial

theorem mun_product_range_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → 0 ≤ t k) :
    0 ≤ (∏ k ∈ Finset.Icc a b, (t k : K)) :=
  Finset.prod_nonneg h3

theorem mun_product_single {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) :
    (∏ k ∈ Finset.Icc a a, (t k : K)) = t a :=
  LeanBridges.Sums.product_single t a

theorem mun_product_extended {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (n : ℤ) (h3 : a ≤ n) :
    (∏ k ∈ Finset.Icc a (n + 1), (t k : K)) = (∏ k ∈ Finset.Icc a n, (t k : K)) * t (n + 1) :=
  LeanBridges.Sums.product_extended t a n h3

theorem mun_product_first {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : a ≤ b) :
    (∏ k ∈ Finset.Icc a b, (t k : K)) = t a * (∏ k ∈ Finset.Icc (a + 1) b, (t k : K)) :=
  by rw [(show Finset.Icc a b = insert a (Finset.Icc (a + 1) b) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega), Finset.prod_insert (by simp)]

theorem mun_product_termwise {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (X : Set ℤ) (Z : Set K) (Y : Set ℤ) (W : Set K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k = u k) (ht : Set.MapsTo t X Z) (hu : Set.MapsTo u Y W) :
    (∏ k ∈ Finset.Icc a b, (t k : K)) = (∏ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.prod_congr rfl h3

theorem mun_range_difference (a : ℤ) (n : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a n) :
    0 ≤ n - k :=
  LeanBridges.Sums.range_difference a n k h3

theorem mun_range_integer (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    True :=
  by simp_all

theorem mun_range_nat0 (n : ℤ) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ k :=
  (Finset.mem_Icc.mp h2).1

theorem mun_range_nat (n : ℤ) (k : ℤ) (h2 : k ∈ Finset.Icc (1 : ℤ) n) :
    0 < k :=
  by (aesop)

theorem def_range (k : ℤ) (n : ℤ) :
    k ∈ Finset.Icc (1 : ℤ) n ↔ 0 < k ∧ k ≤ n :=
  by rw [Finset.mem_Icc]; omega

theorem def_range0 (k : ℤ) (n : ℤ) (h1 : 0 ≤ n) :
    k ∈ Finset.Icc (0 : ℤ) n ↔ 0 ≤ k ∧ k ≤ n :=
  Finset.mem_Icc

theorem mun_range_single (m : ℤ) :
    (Set.Icc m m : Set ℤ) = ({m} : Set ℤ) :=
  by (simp_all; done)

theorem mun_range_empty :
    (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ :=
  by (simp_all; done)

theorem mun_range_split (m : ℤ) (n : ℤ) (k : ℤ) (h1 : k ∈ Finset.Icc m n) :
    (Set.Icc m n : Set ℤ) = (Set.Icc m k : Set ℤ) ∪ (Set.Icc (k + 1) n : Set ℤ) :=
  by simp only [Finset.mem_Icc] at h1; ext x; simp only [Set.mem_union, Set.mem_Icc]; omega

theorem mun_range_extended (a : ℤ) (b : ℤ) (k : ℤ) (h1 : k ∈ Finset.Icc a b) :
    k ∈ Finset.Icc a (b + 1) :=
  by simp only [Finset.mem_Icc] at h1 ⊢; omega

theorem mun_range_without_last (n : ℤ) (h1 : 0 < n) :
    (Set.Icc (1 : ℤ) n : Set ℤ) = (Set.Icc (1 : ℤ) (n + 1) : Set ℤ) \ ({n + 1} : Set ℤ) :=
  by aesop

theorem mun_range_end (n : ℤ) (h1 : 0 < n) :
    n ∈ Finset.Icc (1 : ℤ) n :=
  by aesop

theorem mun_range_within (a : ℤ) (k : ℤ) (n : ℤ) (h4 : k ≤ n) :
    (Set.Icc a k : Set ℤ) ⊆ (Set.Icc a n : Set ℤ) :=
  Set.Icc_subset_Icc_right h4

theorem mun_range_inside (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (h5 : c ≤ a) (h6 : b ≤ d) :
    (Set.Icc a b : Set ℤ) ⊆ (Set.Icc c d : Set ℤ) :=
  Set.Icc_subset_Icc h5 h6

theorem def_range_between (k : ℤ) (a : ℤ) (b : ℤ) :
    k ∈ Finset.Icc a b ↔ a ≤ k ∧ k ≤ b :=
  Finset.mem_Icc

theorem mun_range_bounds_1 (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    a ≤ k :=
  (Finset.mem_Icc.mp h3).1

theorem mun_range_bounds_2 (a : ℤ) (b : ℤ) (k : ℤ) (h3 : k ∈ Finset.Icc a b) :
    k ≤ b :=
  (Finset.mem_Icc.mp h3).2

theorem mun_sum_split {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (c : ℤ) (h4 : a ≤ b + 1) (h5 : b ≤ c) :
    (∑ k ∈ Finset.Icc a c, (t k : K)) = (∑ k ∈ Finset.Icc a b, (t k : K)) + (∑ k ∈ Finset.Icc (b + 1) c, (t k : K)) :=
  LeanBridges.Sums.sum_split t a b c h4 h5

theorem mun_sum_le {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (u : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → t k ≤ u k) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) ≤ (∑ k ∈ Finset.Icc a b, (u k : K)) :=
  Finset.sum_le_sum h3

theorem mun_sum_constant {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : ℤ) (b : ℤ) (h3 : a ≤ b) (c : K) :
    (∑ k ∈ Finset.Icc a b, (c : K)) = ((b : K) - (a : K) + 1) * c :=
  LeanBridges.Sums.sum_constant a b h3 c

theorem mun_sum_constant_over {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {α : Type*} (X : Set α) (h1 : X.Finite) (c : K) :
    (∑ᶠ x ∈ X, (c : K)) = (X.ncard : K) * c :=
  by rw [finsum_mem_eq_finite_toFinset_sum _ h1, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ h1]

theorem mun_sum_empty_range {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : b < a) :
    (∑ k ∈ Finset.Icc a b, (t k : K)) = 0 :=
  by (simp_all; done)

theorem mun_sum_empty_set {K : Type*} [CommRing K] [IsDomain K] (t : ℤ → K) :
    (∑ᶠ k ∈ (∅ : Set ℤ), (t k : K)) = 0 :=
  by exact finsum_mem_empty

theorem mun_sum_of_three {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (b : K) (c : K) (h4 : a ≠ b) (h5 : a ≠ c) (h6 : b ≠ c) :
    (∑ᶠ d ∈ ({a, b, c} : Set K), (d : K)) = a + b + c :=
  by rw [finsum_mem_insert _ (by simp [h4, h5]) (Set.toFinite _), finsum_mem_pair h6]; ring

theorem mun_sum_nonneg {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → 0 ≤ t k) :
    0 ≤ (∑ k ∈ Finset.Icc a b, (t k : K)) :=
  Finset.sum_nonneg h3

theorem mun_sum_zero_terms {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (t : ℤ → K) (a : ℤ) (b : ℤ) (h3 : ∀ k : ℤ, k ∈ Finset.Icc a b → 0 ≤ t k) (h4 : (∑ k ∈ Finset.Icc a b, (t k : K)) = 0) :
    ∀ k : ℤ, k ∈ Finset.Icc a b → t k = 0 :=
  by exact (Finset.sum_eq_zero_iff_of_nonneg h3).mp h4

theorem mun_range_finite (a : ℤ) (b : ℤ) :
    (Set.Icc a b : Set ℤ).Finite :=
  by simp_all

theorem mun_range_in_integers (a : ℤ) (b : ℤ) :
    (Set.Icc a b : Set ℤ) ⊆ (Set.univ : Set ℤ) :=
  by simp_all

theorem mun_range_from_bounds (m : ℤ) (h1 : 0 < m) (x : ℤ) (h2 : 0 ≤ x) (h3 : x < m) :
    x ∈ Finset.Icc (0 : ℤ) (m - 1) :=
  LeanBridges.Sums.range_from_bounds m h1 x h2 h3

theorem mun_product_integer (X : Set ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) :
    True :=
  by (simp_all; done)

theorem mun_product_split {K : Type*} [CommRing K] [IsDomain K] {α : Type*} (t : α → K) (X : Set α) (Y : Set α) (Z : Set α) (h1 : X.Finite) (h2 : X = Y ∪ Z) (h3 : Y ∩ Z = ∅) :
    (∏ᶠ x ∈ X, (t x : K)) = (∏ᶠ x ∈ Y, (t x : K)) * (∏ᶠ x ∈ Z, (t x : K)) :=
  by subst h2; exact finprod_mem_union (Set.disjoint_iff_inter_eq_empty.mpr h3) (h1.subset Set.subset_union_left) (h1.subset Set.subset_union_right)

theorem mun_product_reindex {K : Type*} [CommRing K] [IsDomain K] {α : Type*} (t : α → K) (Y : Set α) (Z : Set α) (g : α → α) (h1 : Y.Finite) (h2 : Set.MapsTo g Y Z ∧ Set.InjOn g Y ∧ Set.SurjOn g Y Z) :
    (∏ᶠ z ∈ Z, (t z : K)) = (∏ᶠ y ∈ Y, (t (g y) : K)) :=
  by rw [← h2.2.2.image_eq_of_mapsTo h2.1]; exact finprod_mem_image h2.2.1

theorem mun_product_of_products {K : Type*} [CommRing K] [IsDomain K] {α : Type*} (t : α → K) (u : α → K) (X : Set α) (h1 : X.Finite) :
    (∏ᶠ x ∈ X, (t x * u x : K)) = (∏ᶠ x ∈ X, (t x : K)) * (∏ᶠ x ∈ X, (u x : K)) :=
  by exact finprod_mem_mul_distrib h1

theorem mun_product_of_ones {α : Type*} (X : Set α) (h1 : X.Finite) :
    (∏ᶠ x ∈ X, (1 : ℤ)) = 1 :=
  by (simp_all; done)

theorem mun_product_empty {K : Type*} [CommRing K] [IsDomain K] {α : Type*} (X : Set α) (t : α → K) :
    (∏ᶠ x ∈ (∅ : Set α), (t x : K)) = 1 :=
  by exact finprod_mem_empty

theorem mun_product_add_one {K : Type*} [CommRing K] [IsDomain K] {α : Type*} (t : α → K) (X : Set α) (Y : Set α) (a : α) (h1 : Y ∈ 𝒫 X) (h2 : Y.Finite) (h3 : a ∈ X) (h4 : ¬ a ∈ Y) :
    (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (t x : K)) = (∏ᶠ x ∈ Y, (t x : K)) * t a :=
  by rw [Set.union_singleton, finprod_mem_insert _ h4 h2, mul_comm]

theorem mun_product_integer_terms {α : Type*} (t : α → ℤ) (X : Set α) (h1 : X.Finite) :
    ∀ Y ∈ 𝒫 X, True :=
  by exact fun _ _ => trivial

theorem mun_product_constant {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {α : Type*} (X : Set α) (h1 : X.Finite) (c : K) :
    (∏ᶠ x ∈ X, (c : K)) = c ^ X.ncard :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h1, Finset.prod_const, Set.ncard_eq_toFinset_card _ h1]

theorem thm_product_factor (X : Set ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) (c : ℤ) :
    (∏ᶠ x ∈ X, (x * c : ℤ)) = c ^ X.ncard * (∏ᶠ x ∈ X, (x : ℤ)) :=
  by rw [finprod_mem_eq_finite_toFinset_prod _ h2, finprod_mem_eq_finite_toFinset_prod _ h2, Finset.prod_mul_distrib, Finset.prod_const, Set.ncard_eq_toFinset_card _ h2]; ring

theorem thm_product_reorder (X : Set ℤ) (f : ℤ → ℤ) (h1 : X ⊆ (Set.univ : Set ℤ)) (h2 : X.Finite) (h3 : Set.MapsTo f X X ∧ Set.InjOn f X) :
    (∏ᶠ x ∈ X, (f x : ℤ)) = (∏ᶠ x ∈ X, (x : ℤ)) :=
  by have hb := (h2.injOn_iff_bijOn_of_mapsTo h3.1).mp h3.2; have hi := finprod_mem_image (f := fun y : ℤ => y) h3.2; rw [← hi, hb.image_eq]

end Parley.Items.Stdlib.Sums
