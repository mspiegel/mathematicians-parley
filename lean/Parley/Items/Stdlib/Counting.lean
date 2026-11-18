module

public import Counting
public import Functions
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Lift
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

/-! Written from corpus/stdlib/counting.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Counting

theorem def_factorial_1 :
    (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.factorial_1

theorem def_factorial_2 :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.factorial_2

theorem def_factorial_3 (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial (n + 1) : ℤ) = (LeanBridges.Counting.factorial n : ℤ) * (n + 1) :=
  LeanBridges.Counting.factorial_3 n h1

theorem mun_factorial_nat (n : ℤ) (h1 : 0 ≤ n) :
    0 < (LeanBridges.Counting.factorial n : ℤ) :=
  LeanBridges.Counting.factorial_nat n h1

theorem mun_factorial_product (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial n : ℤ) = (∏ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) :=
  by lift n to ℕ using h1; induction n with | zero => simp | succ k ih => (rw [(show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring), LeanBridges.Counting.factorial_3 (k : ℤ) (by positivity), ih, (show Finset.Icc (1 : ℤ) ((k : ℤ) + 1) = insert ((k : ℤ) + 1) (Finset.Icc 1 (k : ℤ)) by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega), Finset.prod_insert (by simp), mul_comm])

theorem mun_factorial_at_most (m : ℤ) (h1 : 0 ≤ m) (n : ℤ) (h2 : 0 ≤ n) (h3 : m ≤ n) :
    (LeanBridges.Counting.factorial m : ℤ) ≤ (LeanBridges.Counting.factorial n : ℤ) :=
  LeanBridges.Counting.factorial_at_most m h1 n h2 h3

theorem mun_factorial_divisible (n : ℤ) (h1 : 0 < n) (m : ℤ) (h2 : 0 < m) (h3 : m ≤ n) :
    m ∣ (LeanBridges.Counting.factorial n : ℤ) :=
  LeanBridges.Counting.factorial_divisible n h1 m h2 h3

theorem mun_card_zero {α : Type*} [Nonempty α] (X : Set α) (h1 : X.encard = ((0 : ℕ) : ℕ∞)) :
    X = ∅ :=
  Set.encard_eq_zero.mp (by simpa using h1)

theorem mun_card_singleton {α : Type*} [Nonempty α] (x : α) :
    (({x} : Set α).ncard : ℤ) = 1 :=
  by simp

theorem mun_card_nonempty {α : Type*} [Nonempty α] (X : Set α) (k : ℤ) (h1 : 0 ≤ k) (h2 : (X.ncard : ℤ) = k + 1) :
    ∃ a ∈ X, True :=
  (Set.nonempty_of_ncard_ne_zero (by omega)).imp fun _ h => ⟨h, trivial⟩

theorem mun_card_remove {α : Type*} [Nonempty α] (X : Set α) (a : α) (h1 : a ∈ X) (k : ℤ) (h2 : 0 ≤ k) (h3 : (X.ncard : ℤ) = k + 1) :
    ((X \ ({a} : Set α)).ncard : ℤ) = k :=
  by rw [Set.ncard_diff_singleton_of_mem h1]; omega

theorem mun_card_bijection {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (m : ℤ) (h1 : 0 ≤ m) (h2 : X.encard = ((m.toNat : ℕ) : ℕ∞)) (h3 : ∃ g : α → β, Set.BijOn g X Y) :
    Y.encard = ((m.toNat : ℕ) : ℕ∞) :=
  by obtain ⟨g, hg⟩ := h3; rw [← hg.image_eq, hg.injOn.encard_image, h2]

theorem mun_card_disjoint_union {α : Type*} [Nonempty α] (X : Set α) (Y : Set α) (m : ℤ) (h1 : 0 ≤ m) (n : ℤ) (h2 : 0 ≤ n) (h3 : X.encard = ((m.toNat : ℕ) : ℕ∞)) (h4 : Y.encard = ((n.toNat : ℕ) : ℕ∞)) (h5 : X ∩ Y = ∅) :
    ((X ∪ Y).ncard : ℤ) = m + n :=
  by have hX : X.Finite := Set.finite_of_encard_eq_coe h3; have hY : Y.Finite := Set.finite_of_encard_eq_coe h4; have hm : X.ncard = m.toNat := (by rw [← hX.cast_ncard_eq] at h3; exact_mod_cast h3); have hn : Y.ncard = n.toNat := (by rw [← hY.cast_ncard_eq] at h4; exact_mod_cast h4); rw [Set.ncard_union_eq (Set.disjoint_iff_inter_eq_empty.mpr h5) hX hY, hm, hn]; omega

theorem def_C_1 (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (-1 : ℤ) : ℤ) = 0 :=
  LeanBridges.Counting.C_1 n h1

theorem def_C_2 (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    k ∈ Finset.Icc (0 : ℤ) n → (LeanBridges.Counting.choose n k : ℚ) = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) :=
  LeanBridges.Counting.C_2 n h1 k

theorem def_C_3 (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    n < k → (LeanBridges.Counting.choose n k : ℤ) = 0 :=
  LeanBridges.Counting.C_3 n h1 k

theorem thm_pascal (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    (LeanBridges.Counting.choose n k : ℤ) + (LeanBridges.Counting.choose n (k - 1) : ℤ) = (LeanBridges.Counting.choose (n + 1) k : ℤ) :=
  LeanBridges.Counting.pascal n h1 k

theorem thm_absorption (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) n) :
    (LeanBridges.Counting.choose (n + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose n k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) :=
  LeanBridges.Counting.absorption n h1 k h2

theorem mun_binomial_zero_index (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (0 : ℤ) : ℤ) = 1 :=
  LeanBridges.Counting.binomial_zero_index n h1

theorem mun_binomial_one (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n :=
  LeanBridges.Counting.binomial_one n h1

theorem mun_binomial_all (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n n : ℤ) = 1 :=
  LeanBridges.Counting.binomial_all n h1

theorem mun_binomial_two (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
  LeanBridges.Counting.binomial_two n h1

theorem mun_binomial_outside (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) (h3 : ¬ k ∈ Finset.Icc (0 : ℤ) n) :
    (LeanBridges.Counting.choose n k : ℤ) = 0 :=
  LeanBridges.Counting.choose_outside n h1 k h3

theorem mun_binomial_nat0 (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) :
    0 ≤ (LeanBridges.Counting.choose n k : ℤ) :=
  LeanBridges.Counting.binomial_nat0 n h1 k

theorem mun_binomial_nat (n : ℤ) (h1 : 0 ≤ n) (k : ℤ) (h2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 < (LeanBridges.Counting.choose n k : ℤ) :=
  LeanBridges.Counting.choose_pos n h1 k h2

theorem mun_card_empty {α : Type*} [Nonempty α] :
    ((∅ : Set α).ncard : ℤ) = 0 :=
  by simp

theorem mun_finite_part {α : Type*} [Nonempty α] (X : Set α) (Y : Set α) (h1 : X.Finite) (h2 : Y ⊆ X) :
    Y.Finite :=
  h1.subset h2

theorem mun_factorial_nonzero (n : ℤ) (h1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial n : ℤ) ≠ 0 :=
  LeanBridges.Counting.factorial_nonzero n h1

theorem mun_union_finite {α : Type*} [Nonempty α] (X : Set α) (Y : Set α) (h1 : X.Finite) (h2 : Y.Finite) :
    (X ∪ Y).Finite :=
  by simp_all

theorem mun_card_nat0 {α : Type*} [Nonempty α] (X : Set α) (h1 : X.Finite) :
    0 ≤ (X.ncard : ℤ) :=
  Int.natCast_nonneg _

theorem mun_card_finite {α : Type*} [Nonempty α] (X : Set α) (m : ℤ) (h1 : 0 ≤ m) (h2 : X.encard = ((m.toNat : ℕ) : ℕ∞)) :
    X.Finite :=
  Set.finite_of_encard_eq_coe h2

theorem mun_card_difference {α : Type*} [Nonempty α] (X : Set α) (Y : Set α) (h1 : X.Finite) (h2 : Y ⊆ X) :
    ((X \ Y).ncard : ℤ) = (X.ncard : ℤ) - (Y.ncard : ℤ) :=
  Set.cast_ncard_sdiff h2 h1

theorem mun_card_at_least_one {α : Type*} [Nonempty α] (X : Set α) (h1 : ¬ X = ∅) :
    ((1 : ℕ) : ℕ∞) ≤ X.encard :=
  LeanBridges.Counting.card_at_least_one X h1

theorem mun_parts_finite {α : Type*} [Nonempty α] (A : Set α) (K : Set (Set α)) (h1 : A.Finite) (h2 : ∀ Y ∈ K, Y ⊆ A) :
    K.Finite :=
  (h1.finite_subsets).subset (fun Y hY => h2 Y hY)

theorem mun_card_equal {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (h1 : X.Finite) (h2 : ∃ g : α → β, Set.BijOn g X Y) :
    ((X.ncard : ℕ) : ℕ∞) = Y.encard :=
  by obtain ⟨g, hg⟩ := h2; rw [h1.cast_ncard_eq, ← hg.image_eq, hg.injOn.encard_image]

theorem mun_partition_count {α : Type*} [Nonempty α] (A : Set α) (K : Set (Set α)) (m : ℤ) (h1 : 0 ≤ m) (h2 : A.Finite) (h3 : (⋃ Y ∈ K, Y) = A) (h4 : ∀ Y ∈ K, ∀ Z ∈ K, ∀ x ∈ Y ∩ Z, Y = Z) (h5 : ∀ Y ∈ K, Y.encard = ((m.toNat : ℕ) : ℕ∞)) :
    ((A.ncard : ℕ) : ℕ∞) = K.encard * ((m.toNat : ℕ) : ℕ∞) :=
  LeanBridges.Counting.partition_count A K m h1 h2 h3 h4 h5

theorem mun_count_nat0 (P : ℤ → Prop) (k : ℤ) :
    0 ≤ ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i}.ncard : ℤ) :=
  LeanBridges.Counting.count_nat0 P k

theorem mun_count_empty_range (P : ℤ → Prop) :
    ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | P i}.ncard : ℤ) = 0 :=
  LeanBridges.Counting.count_empty_range P

theorem mun_count_step_holds (P : ℤ → Prop) (k : ℤ) (h1 : 0 ≤ k) (h2 : P (k + 1)) :
    ({i ∈ (Set.Icc (1 : ℤ) (k + 1) : Set ℤ) | P i}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i}.ncard : ℤ) + 1 :=
  LeanBridges.Counting.count_step_holds P k h1 h2

theorem mun_count_step_fails (P : ℤ → Prop) (k : ℤ) (h1 : 0 ≤ k) (h2 : ¬ P (k + 1)) :
    ({i ∈ (Set.Icc (1 : ℤ) (k + 1) : Set ℤ) | P i}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i}.ncard : ℤ) :=
  LeanBridges.Counting.count_step_fails P k h1 h2

theorem mun_count_same (P : ℤ → Prop) (Q : ℤ → Prop) (n : ℤ) (h2 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → (P i ↔ Q i)) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | Q i}.ncard : ℤ) :=
  LeanBridges.Counting.count_same P Q n h2

theorem mun_count_either (P : ℤ → Prop) (Q : ℤ → Prop) (n : ℤ) (h2 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → ¬ (P i ∧ Q i)) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i ∨ Q i}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}.ncard : ℤ) + ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | Q i}.ncard : ℤ) :=
  LeanBridges.Counting.count_either P Q n h2

theorem mun_count_shift (P : ℤ → Prop) (n : ℤ) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P (i - 1)}.ncard : ℤ) = ({i ∈ (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) | P i}.ncard : ℤ) :=
  LeanBridges.Counting.count_shift P n

theorem mun_count_first_fails (P : ℤ → Prop) (m : ℤ) (h2 : ¬ P (0 : ℤ)) :
    ({i ∈ (Set.Icc (0 : ℤ) m : Set ℤ) | P i}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) m : Set ℤ) | P i}.ncard : ℤ) :=
  LeanBridges.Counting.count_first_fails P m h2

theorem mun_count_last_fails (P : ℤ → Prop) (n : ℤ) (h2 : ¬ P n) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) (n - 1) : Set ℤ) | P i}.ncard : ℤ) :=
  LeanBridges.Counting.count_last_fails P n h2

theorem mun_card_pair {α : Type*} [Nonempty α] (u : α) (w : α) :
    (({u, w} : Set α).ncard : ℤ) ≤ 2 :=
  by have h := Set.ncard_insert_le u ({w} : Set α); rw [Set.ncard_singleton] at h; exact_mod_cast h

theorem mun_card_subset {α : Type*} [Nonempty α] (A : Set α) (B : Set α) (h1 : A ⊆ B) :
    A.encard ≤ B.encard :=
  Set.encard_le_encard h1

theorem mun_card_pair_distinct {α : Type*} [Nonempty α] (u : α) (w : α) :
    ¬ u = w ↔ (({u, w} : Set α).ncard : ℤ) = 2 :=
  by constructor; (intro h; exact_mod_cast Set.ncard_pair h); (intro h huw; subst huw; simp at h)

theorem mun_card_two {α : Type*} [Nonempty α] (Y : Set α) (a : α) (b : α) (h1 : (Y.ncard : ℤ) = 2) (h2 : a ∈ Y) (h3 : b ∈ Y) (h4 : ¬ a = b) :
    Y = ({a, b} : Set α) :=
  LeanBridges.Counting.card_two Y a b h1 h2 h3 h4

theorem mun_card_positive {α : Type*} [Nonempty α] (X : Set α) (h1 : ((0 : ℕ) : ℕ∞) < X.encard) :
    ¬ X = ∅ :=
  LeanBridges.Counting.card_positive X h1

theorem mun_range_size (n : ℤ) (h1 : 0 ≤ n) :
    ((Set.Icc (1 : ℤ) n : Set ℤ).ncard : ℤ) = n :=
  by rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]; omega

theorem mun_card_add_one {α : Type*} [Nonempty α] (X : Set α) (a : α) (h1 : X.Finite) (h2 : ¬ a ∈ X) :
    ((X ∪ ({a} : Set α)).ncard : ℤ) = (X.ncard : ℤ) + 1 :=
  by rw [Set.union_singleton, Set.ncard_insert_of_notMem h2 h1]; push_cast; ring

theorem mun_card_product {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (h1 : X.Finite) (h2 : Y.Finite) :
    ((X ×ˢ Y).ncard : ℤ) = (X.ncard : ℤ) * (Y.ncard : ℤ) :=
  by rw [Set.ncard_prod, Nat.cast_mul]

theorem thm_pigeonhole {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (f : α → β) (h1 : Set.MapsTo f X Y ∧ Set.InjOn f X) :
    X.encard ≤ Y.encard :=
  by rw [← h1.2.encard_image]; exact Set.encard_le_encard (h1.1.image_subset)

theorem thm_count_functions {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (h1 : X.Finite) (h2 : Y.Finite) :
    ((LeanBridges.Functions.functions_from X Y).ncard : ℤ) = (Y.ncard : ℤ) ^ X.ncard :=
  by obtain ⟨m, hm, he⟩ := LeanBridges.Counting.count_functions X Y h1 h2; rw [Set.ncard_def, hm, ENat.toNat_natCast]; exact he

theorem thm_count_one_to_one {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (h1 : X.Finite) (h2 : Y.Finite) (h3 : (X.ncard : ℤ) ≤ (Y.ncard : ℤ)) :
    ({f ∈ LeanBridges.Functions.functions_from X Y | Set.MapsTo f Set.univ Y ∧ Set.InjOn f Set.univ}.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) ((X.ncard : ℤ) - 1), ((Y.ncard : ℤ) - k : ℤ)) :=
  by obtain ⟨m, hm, he⟩ := LeanBridges.Counting.count_one_to_one X Y h1 h2 h3; rw [Set.ncard_def, hm, ENat.toNat_natCast]; exact he

end Parley.Items.Stdlib.Counting
