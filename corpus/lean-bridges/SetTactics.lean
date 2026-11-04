module

public import Mathlib
public import Tactics

/-!
# What a page about sets leaves to its reader

`parley_side`, and after it the ways a goal about sets is closed: finite
sets compared or counted member by member, and a membership of a listed set
taken case by case. A generated file whose statements or steps use sets
calls `parley_set_side` where any other calls `parley_side`
(`build::lean`), so that a change here rebuilds only those files.
-/

public section

/-! The page's ℕ and ℕ₀ stand as sets of integers, `{n : ℤ | 0 < n}` and
`{n : ℤ | 0 ≤ n}`, and a letter of them as a natural number: these say a
property of every or some such integer is that of every or some natural. -/

theorem parley_forall_pos (P : ℤ → Prop) : (∀ s : ℤ, 0 < s → P s) ↔ ∀ n : ℕ, 0 < n → P n :=
  ⟨fun h n hn => h n (by exact_mod_cast hn), fun h s hs => by
    lift s to ℕ using hs.le; exact h s (by exact_mod_cast hs)⟩

theorem parley_exists_pos (P : ℤ → Prop) : (∃ s : ℤ, 0 < s ∧ P s) ↔ ∃ n : ℕ, 0 < n ∧ P n :=
  ⟨fun ⟨s, hs, h⟩ => by lift s to ℕ using hs.le; exact ⟨s, by exact_mod_cast hs, h⟩,
   fun ⟨n, hn, h⟩ => ⟨n, by exact_mod_cast hn, h⟩⟩

theorem parley_forall_nonneg (P : ℤ → Prop) : (∀ s : ℤ, 0 ≤ s → P s) ↔ ∀ n : ℕ, P n :=
  ⟨fun h n => h n (by positivity), fun h s hs => by lift s to ℕ using hs; exact h s⟩

theorem parley_exists_nonneg (P : ℤ → Prop) : (∃ s : ℤ, 0 ≤ s ∧ P s) ↔ ∃ n : ℕ, P n :=
  ⟨fun ⟨s, hs, h⟩ => by lift s to ℕ using hs; exact ⟨s, h⟩, fun ⟨n, h⟩ => ⟨n, by positivity, h⟩⟩

/-- `parley_side`, then the ways of sets. -/
macro "parley_set_side" : tactic =>
  `(tactic| first
    -- Something said of every or some member of the page's ℕ or ℕ₀, the
    -- integers above or from 0, of a line that says it of natural numbers;
    -- a map into all of a type maps anything there. This and the next are
    -- tried before `parley_side`, whose last way, `simp_all`, recurses
    -- past Lean's limit beside a set a define builds and a line x = e(x),
    -- a = a·1 + b·0, which `first` does not recover from.
    | (simp only [Set.mem_ofPred_eq, Set.mem_univ, Set.mapsTo_univ, true_and, true_implies,
         forall_const, parley_forall_pos, parley_exists_pos, parley_forall_nonneg,
         parley_exists_nonneg];
       and_intros <;> first | assumption | omega | (exact ⟨_, ‹_›⟩) | (exact ⟨_, _, ‹_›⟩) | (exact ⟨_, _, rfl⟩))
    -- There is some member of a set, of a member a line names.
    | (exact ⟨_, ‹_ ∈ _›, trivial⟩)
    | parley_side
    -- Two finite sets of numbers equal, {x ∈ {−3, −2, 0, 5} : x is odd} =
    -- {−3, 5}: member by member, each case decided.
    | (ext x; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff];
       constructor <;> intro h <;> (try casesm* _ ∨ _, _ ∧ _) <;> (try subst_vars) <;>
       simp_all (config := {decide := true}); done)
    -- A count of a finite set the page lists or builds, |{1, 2}| = 2:
    -- counted as a Finset, each member decided.
    | (rw [Set.encard_eq_coe_toFinset_card];
       simp (config := {decide := true})
         [Set.toFinset_insert, Set.toFinset_singleton, Set.toFinset_setOf]; done)
    -- One of a listed set, x ∈ {a, b}, taken case by case.
    | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *;
       rcases ‹_ ∨ _› with h | h <;> simp [h]; done)
    -- One of a range of integers, x ∈ S with S = {3, …, 5}: its bounds,
    -- and the integers between them.
    | (subst_vars; simp only [Set.mem_Icc] at *; omega)
    -- A pair a line says, in the other order: {a, b} is {b, a}, a listed
    -- set's order being none of the page's.
    | (rw [Set.pair_comm]; assumption)
    -- A map's value at a member of its domain, f(a) > 0 of f : ℕ → ℕ:
    -- the page's ℕ is the integers above 0, which a natural a is among.
    | (simp only [Set.MapsTo, Set.mem_ofPred_eq] at *; apply_assumption; omega))
