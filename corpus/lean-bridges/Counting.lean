module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Computability.Reduce
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Lean.Parser.Command
public import Factorials
public import Functions
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard

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
theorem card_two {α : Type*} (Y : Set α) (a : α) (b : α) (h1 : (Y.ncard : ℤ) = 2) (h2 : a ∈ Y) (h3 : b ∈ Y) (h4 : ¬ a = b) :
    Y = ({a, b} : Set α) :=
  (Set.eq_of_subset_of_ncard_le (Set.insert_subset_iff.mpr ⟨h2, Set.singleton_subset_iff.mpr h3⟩) (by rw [Set.ncard_pair h4]; omega) (Set.finite_of_ncard_ne_zero (by omega))).symm

/-- `mun:stdlib/counting/card-positive`. -/
theorem card_positive {α : Type*} (X : Set α) (h1 : ((0 : ℕ) : ℕ∞) < X.encard) :
    ¬ X = ∅ :=
  by intro h; subst h; simp at h1

/-- `mun:stdlib/counting/partition-count`. The parts lie in A, so there are
finitely many, and parts that meet are equal, so they are disjoint. -/
theorem partition_count {α : Type*} (A : Set α) (K : Set (Set α)) (m : ℤ) (_h1 : 0 ≤ m)
    (h2 : A.Finite) (h3 : (⋃ Y ∈ K, Y) = A) (h4 : ∀ Y ∈ K, ∀ Z ∈ K, ∀ x ∈ Y ∩ Z, Y = Z)
    (h5 : ∀ Y ∈ K, Y.encard = ((m.toNat : ℕ) : ℕ∞)) :
    ((A.ncard : ℕ) : ℕ∞) = K.encard * ((m.toNat : ℕ) : ℕ∞) := by
  have hsub : K ⊆ 𝒫 A := fun Y hY => h3 ▸ Set.subset_biUnion_of_mem (u := id) hY
  have hK : K.Finite := h2.powerset.subset hsub
  have hdis : K.PairwiseDisjoint id := by
    intro Y hY Z hZ hne
    rw [Function.onFun, Set.disjoint_iff]
    rintro x hx
    exact hne (h4 Y hY Z hZ x hx)
  have hU : (⋃ Y ∈ K, Y).encard = ∑ᶠ Y ∈ K, Y.encard := hK.encard_biUnion (s := id) hdis
  rw [h2.cast_ncard_eq, ← h3, hU, finsum_mem_congr rfl h5,
    finsum_mem_eq_finite_toFinset_sum _ hK, Finset.sum_const, nsmul_eq_mul,
    ← hK.cast_ncard_eq, Set.ncard_eq_toFinset_card K hK]

open LeanBridges.Functions in
/-- The functions from X to Y are the functions from ↥X to ↥Y, each followed
by Y's inclusion in its type. -/
theorem functions_from_eq_range {α β : Type*} (X : Set α) (Y : Set β) :
    functions_from X Y = Set.range (fun g : ↥X → ↥Y => Subtype.val ∘ g) := by
  ext g
  constructor
  · intro hg
    exact ⟨fun x => ⟨g x, hg x⟩, rfl⟩
  · rintro ⟨h, rfl⟩ x
    exact (h x).2

open LeanBridges.Functions in
/-- `thm:stdlib/counting/count-functions`: as many as the functions from ↥X
to ↥Y, |Y|^|X| (`Nat.card_fun`). -/
theorem count_functions {α β : Type*} (X : Set α) (Y : Set β) (h1 : X.Finite) (h2 : Y.Finite) :
    ∃ m : ℕ, (functions_from X Y).encard = (m : ℕ∞) ∧ (m : ℤ) = (Y.ncard : ℤ) ^ X.ncard := by
  have := h1.to_subtype
  have := h2.to_subtype
  have hinj : Function.Injective (fun g : ↥X → ↥Y => Subtype.val ∘ g) :=
    fun g h e => funext fun x => Subtype.ext (congrFun e x)
  refine ⟨Y.ncard ^ X.ncard, ?_, by push_cast; rfl⟩
  rw [functions_from_eq_range, hinj.encard_range, ENat.card_eq_coe_natCard, Nat.card_fun,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq]

open LeanBridges.Functions in
/-- The one-to-one functions from X to Y are the embeddings of ↥X in ↥Y,
each followed by Y's inclusion in its type. -/
theorem one_to_one_eq_range {α β : Type*} (X : Set α) (Y : Set β) :
    {f ∈ functions_from X Y | Set.MapsTo f Set.univ Y ∧ Set.InjOn f Set.univ}
      = Set.range (fun e : ↥X ↪ ↥Y => Subtype.val ∘ e) := by
  ext g
  constructor
  · rintro ⟨hg, -, hinj⟩
    exact ⟨⟨fun x => ⟨g x, hg x⟩, fun a b e =>
      hinj (Set.mem_univ _) (Set.mem_univ _) (congrArg Subtype.val e)⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨fun x => (e x).2, fun x _ => (e x).2,
      fun a _ b _ h => e.injective (Subtype.ext h)⟩

open LeanBridges.Functions in
/-- `thm:stdlib/counting/count-one-to-one`: as many as the embeddings of ↥X
in ↥Y, |Y|·(|Y| − 1)·…·(|Y| − |X| + 1) (`Fintype.card_embedding_eq`), each
factor whole as |X| ≤ |Y|. -/
theorem count_one_to_one {α β : Type*} (X : Set α) (Y : Set β) (h1 : X.Finite) (h2 : Y.Finite)
    (h3 : (X.ncard : ℤ) ≤ (Y.ncard : ℤ)) :
    ∃ m : ℕ, {f ∈ functions_from X Y | Set.MapsTo f Set.univ Y ∧ Set.InjOn f Set.univ}.encard
      = (m : ℕ∞) ∧ (m : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) ((X.ncard : ℤ) - 1), ((Y.ncard : ℤ) - k : ℤ)) := by
  classical
  have := h1.fintype
  have := h2.fintype
  refine ⟨Y.ncard.descFactorial X.ncard, ?_, ?_⟩
  · have hinj : Function.Injective (fun e : ↥X ↪ ↥Y => Subtype.val ∘ e) :=
      fun e e' h => Function.Embedding.ext fun x => Subtype.ext (congrFun h x)
    rw [one_to_one_eq_range, hinj.encard_range, ENat.card_eq_coe_fintype_card,
      Fintype.card_embedding_eq, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  · have hle : X.ncard ≤ Y.ncard := by exact_mod_cast h3
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_nbij' (fun i : ℕ => (i : ℤ)) (fun k : ℤ => k.toNat) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro i _; simp
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Int.toNat_of_nonneg hk.1]
    · intro i hi
      simp only [Finset.mem_range] at hi
      push_cast [Nat.cast_sub (by omega : i ≤ Y.ncard)]
      rfl

/-- The parts of a finite Y with j elements, in the two forms the build
writes them: a part of a set not known finite counted as some natural
number, `∃ m : ℕ, S.encard = m ∧ m = j`, and one of a finite set counted in
ℕ, `S.ncard = j`. Every part of a finite Y is finite, so the two are one
set. -/
theorem builder_count_spelt {α : Type*} (Y : Set α) (hY : Y.Finite) (j : ℤ) :
    {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} = {S ∈ 𝒫 Y | (S.ncard : ℤ) = j} := by
  ext S
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hS, m, hm, he⟩
    refine ⟨hS, ?_⟩
    rw [← he, Set.ncard_def, hm, ENat.toNat_natCast]
  · rintro ⟨hS, h⟩
    exact ⟨hS, S.ncard, ((hY.subset hS).cast_ncard_eq).symm, h⟩

/-- A count a statement writes as some natural number, `∃ m : ℕ, S.encard =
m ∧ P m`, where S is not known finite there, is P of S's count where it is
finite: deg(x) is odd of a finite graph. -/
theorem some_count_iff {α : Type*} {S : Set α} {P : ℕ → Prop} (h : S.Finite) :
    (∃ m : ℕ, S.encard = (m : ℕ∞) ∧ P m) ↔ P S.ncard :=
  ⟨fun ⟨m, hm, hp⟩ => by
      have : S.ncard = m := by
        have := h.cast_ncard_eq; rw [hm] at this; exact_mod_cast this
      rw [this]; exact hp,
    fun hp => ⟨S.ncard, h.cast_ncard_eq.symm, hp⟩⟩

/-! Counts of the integers in a range that have a property: what a walk's
places count in `proofs/wiedijk/konigsberg.proof`. -/

/-- The integers in a range that have a property are finitely many. -/
theorem sep_Icc_finite (P : ℤ → Prop) (a b : ℤ) : {i ∈ (Set.Icc a b : Set ℤ) | P i}.Finite :=
  (Set.finite_Icc a b).subset (fun _ h => h.1)

/-- `mun:stdlib/counting/count-nat0`. -/
theorem count_nat0 (P : ℤ → Prop) (k : ℤ) :
    0 ≤ ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i}.ncard : ℤ) :=
  Int.natCast_nonneg _

/-- `mun:stdlib/counting/count-empty-range`. -/
theorem count_empty_range (P : ℤ → Prop) :
    ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | P i}.ncard : ℤ) = 0 := by
  have : {i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | P i} = ∅ := by
    ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]; omega
  rw [this]; simp

/-- `mun:stdlib/counting/count-step-holds`. -/
theorem count_step_holds (P : ℤ → Prop) (k : ℤ) (_h1 : 0 ≤ k) (h2 : P (k + 1)) :
    ({i ∈ (Set.Icc (1 : ℤ) (k + 1) : Set ℤ) | P i}.ncard : ℤ) =
      ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i}.ncard : ℤ) + 1 := by
  have e : {i ∈ (Set.Icc (1 : ℤ) (k + 1) : Set ℤ) | P i} =
      insert (k + 1) {i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i} := by
    ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_insert_iff]
    constructor
    · rintro ⟨⟨h3, h4⟩, hp⟩
      rcases lt_or_eq_of_le h4 with h5 | h5
      · exact Or.inr ⟨⟨h3, by omega⟩, hp⟩
      · exact Or.inl h5
    · rintro (rfl | ⟨⟨h3, h4⟩, hp⟩)
      · exact ⟨⟨by omega, le_refl _⟩, h2⟩
      · exact ⟨⟨h3, by omega⟩, hp⟩
  rw [e, Set.ncard_insert_of_notMem (by simp only [Set.mem_ofPred_eq, Set.mem_Icc]; omega)
    (sep_Icc_finite P 1 k)]
  push_cast; ring

/-- `mun:stdlib/counting/count-step-fails`. -/
theorem count_step_fails (P : ℤ → Prop) (k : ℤ) (_h1 : 0 ≤ k) (h2 : ¬ P (k + 1)) :
    ({i ∈ (Set.Icc (1 : ℤ) (k + 1) : Set ℤ) | P i}.ncard : ℤ) =
      ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | P i}.ncard : ℤ) := by
  congr 2
  ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h3, h4⟩, hp⟩
    rcases lt_or_eq_of_le h4 with h5 | h5
    · exact ⟨⟨h3, by omega⟩, hp⟩
    · exact absurd (h5 ▸ hp) h2
  · rintro ⟨⟨h3, h4⟩, hp⟩
    exact ⟨⟨h3, by omega⟩, hp⟩

/-- `mun:stdlib/counting/count-same`. -/
theorem count_same (P : ℤ → Prop) (Q : ℤ → Prop) (n : ℤ)
    (h2 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → (P i ↔ Q i)) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}.ncard : ℤ) =
      ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | Q i}.ncard : ℤ) := by
  congr 2
  ext i; simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨h, hp⟩ => ⟨h, (h2 i (Finset.mem_Icc.mpr h)).mp hp⟩,
    fun ⟨h, hq⟩ => ⟨h, (h2 i (Finset.mem_Icc.mpr h)).mpr hq⟩⟩

/-- `mun:stdlib/counting/count-either`. -/
theorem count_either (P : ℤ → Prop) (Q : ℤ → Prop) (n : ℤ)
    (h2 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → ¬ (P i ∧ Q i)) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i ∨ Q i}.ncard : ℤ) =
      ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}.ncard : ℤ) +
        ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | Q i}.ncard : ℤ) := by
  have e : {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i ∨ Q i} =
      {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i} ∪ {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | Q i} := by
    ext i; simp only [Set.mem_ofPred_eq, Set.mem_union]; tauto
  have d : Disjoint {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}
      {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | Q i} := by
    rw [Set.disjoint_left]
    rintro i ⟨h, hp⟩ ⟨_, hq⟩
    exact h2 i (Finset.mem_Icc.mpr h) ⟨hp, hq⟩
  rw [e, Set.ncard_union_eq d (sep_Icc_finite P 1 n) (sep_Icc_finite Q 1 n)]
  push_cast; ring

/-- `mun:stdlib/counting/count-shift`. -/
theorem count_shift (P : ℤ → Prop) (n : ℤ) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P (i - 1)}.ncard : ℤ) =
      ({i ∈ (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) | P i}.ncard : ℤ) := by
  have e : {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P (i - 1)} =
      (fun j => j + 1) '' {i ∈ (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) | P i} := by
    ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_image]
    constructor
    · rintro ⟨⟨h3, h4⟩, hp⟩
      exact ⟨i - 1, ⟨⟨by omega, by omega⟩, hp⟩, by ring⟩
    · rintro ⟨j, ⟨⟨h3, h4⟩, hp⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by simpa using hp⟩
  rw [e, Set.ncard_image_of_injective _ (add_left_injective 1)]

/-- `mun:stdlib/counting/count-first-fails`. -/
theorem count_first_fails (P : ℤ → Prop) (m : ℤ) (h2 : ¬ P (0 : ℤ)) :
    ({i ∈ (Set.Icc (0 : ℤ) m : Set ℤ) | P i}.ncard : ℤ) =
      ({i ∈ (Set.Icc (1 : ℤ) m : Set ℤ) | P i}.ncard : ℤ) := by
  congr 2
  ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h3, h4⟩, hp⟩
    rcases lt_or_eq_of_le h3 with h5 | h5
    · exact ⟨⟨by omega, h4⟩, hp⟩
    · exact absurd (h5 ▸ hp) h2
  · rintro ⟨⟨h3, h4⟩, hp⟩
    exact ⟨⟨by omega, h4⟩, hp⟩

/-- `mun:stdlib/counting/count-last-fails`. -/
theorem count_last_fails (P : ℤ → Prop) (n : ℤ) (h2 : ¬ P n) :
    ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | P i}.ncard : ℤ) =
      ({i ∈ (Set.Icc (1 : ℤ) (n - 1) : Set ℤ) | P i}.ncard : ℤ) := by
  congr 2
  ext i; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h3, h4⟩, hp⟩
    rcases lt_or_eq_of_le h4 with h5 | h5
    · exact ⟨⟨h3, by omega⟩, hp⟩
    · exact absurd (h5 ▸ hp) h2
  · rintro ⟨⟨h3, h4⟩, hp⟩
    exact ⟨⟨h3, by omega⟩, hp⟩

end LeanBridges.Counting
