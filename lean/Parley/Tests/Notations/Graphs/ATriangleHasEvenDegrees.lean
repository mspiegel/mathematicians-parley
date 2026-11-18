module

public import Graphs
public import Sets
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Graphs

/-! Written from tests/notations/graphs.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Graphs.ATriangleHasEvenDegrees

theorem a_triangle_has_even_degrees {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (A : α) (B : α) (C : α) (a : β) (b : β) (c : β) (hH1a : V = ({A, B, C} : Set α)) (hH1b : E = ({a, b, c} : Set β)) (hH1c : ¬ A = B) (hH1d : ¬ A = C) (hH1e : ¬ B = C) (hH1f : ¬ a = b) (hH1g : ¬ a = c) (hH1h : ¬ b = c) (hH1i : G a = Sym2.mk A B) (hH1j : G b = Sym2.mk B C) (hH1k : G c = Sym2.mk A C) :
    {a ∈ E | A ∈ G a}.encard = ((2 : ℕ) : ℕ∞) ∧ {x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)}.encard = ((0 : ℕ) : ℕ∞) := by
  -- 1. def:degree
  have s1 : ∀ x ∈ V, {a ∈ E | x ∈ G a}.encard = {s ∈ E | x ∈ G s}.encard := by intro x h_x; (exact (Parley.Items.Stdlib.Graphs.def_degree (E := E) (V := V) (x := x) (G := G) h_x))
  -- 2. inspection, from H1, 1
  have s2 : ({a ∈ E | A ∈ G a}.ncard : ℤ) = 2 := by rw [hH1b]; simp only [LeanBridges.Sets.sep_insert_of (p := (fun a : β => A ∈ G a)) (show A ∈ G a by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_insert_of_not (p := (fun a : β => A ∈ G a)) (show ¬ A ∈ G b by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_singleton_of (p := (fun a : β => A ∈ G a)) (show A ∈ G c by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff])]; norm_num [Set.encard_insert_of_notMem, Set.encard_singleton, hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k]
  -- 3. inspection, from H1, 1
  have s3 : ({a ∈ E | B ∈ G a}.ncard : ℤ) = 2 := by rw [hH1b]; simp only [LeanBridges.Sets.sep_insert_of (p := (fun a : β => B ∈ G a)) (show B ∈ G a by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_insert_of (p := (fun a : β => B ∈ G a)) (show B ∈ G b by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_singleton_of_not (p := (fun a : β => B ∈ G a)) (show ¬ B ∈ G c by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff])]; norm_num [Set.encard_insert_of_notMem, Set.encard_singleton, hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k]
  -- 4. inspection, from H1, 1
  have s4 : ({a ∈ E | C ∈ G a}.ncard : ℤ) = 2 := by rw [hH1b]; simp only [LeanBridges.Sets.sep_insert_of_not (p := (fun a : β => C ∈ G a)) (show ¬ C ∈ G a by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_insert_of (p := (fun a : β => C ∈ G a)) (show C ∈ G b by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_singleton_of (p := (fun a : β => C ∈ G a)) (show C ∈ G c by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, Sym2.mem_iff])]; norm_num [Set.encard_insert_of_notMem, Set.encard_singleton, hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k]
  -- 5. inspection, from H1, 2, 3, 4
  have s5 : {x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)}.encard = ((0 : ℕ) : ℕ∞) := by rw [hH1a]; simp only [LeanBridges.Sets.sep_insert_of_not (p := (fun x : α => ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ))) (show ¬ (∃ m : ℕ, {a ∈ E | A ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)) by simp only [show {a ∈ E | A ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s2; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | A ∈ G a} : Set β).Finite))]; exact_mod_cast s2, show {a ∈ E | B ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s3; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | B ∈ G a} : Set β).Finite))]; exact_mod_cast s3, show {a ∈ E | C ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s4; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | C ∈ G a} : Set β).Finite))]; exact_mod_cast s4, ENat.natCast_inj, exists_eq_left']; decide), LeanBridges.Sets.sep_insert_of_not (p := (fun x : α => ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ))) (show ¬ (∃ m : ℕ, {a ∈ E | B ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)) by simp only [show {a ∈ E | A ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s2; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | A ∈ G a} : Set β).Finite))]; exact_mod_cast s2, show {a ∈ E | B ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s3; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | B ∈ G a} : Set β).Finite))]; exact_mod_cast s3, show {a ∈ E | C ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s4; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | C ∈ G a} : Set β).Finite))]; exact_mod_cast s4, ENat.natCast_inj, exists_eq_left']; decide), LeanBridges.Sets.sep_singleton_of_not (p := (fun x : α => ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ))) (show ¬ (∃ m : ℕ, {a ∈ E | C ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)) by simp only [show {a ∈ E | A ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s2; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | A ∈ G a} : Set β).Finite))]; exact_mod_cast s2, show {a ∈ E | B ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s3; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | B ∈ G a} : Set β).Finite))]; exact_mod_cast s3, show {a ∈ E | C ∈ G a}.encard = ((2 : ℕ) : ℕ∞) by rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s4; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | C ∈ G a} : Set β).Finite))]; exact_mod_cast s4, ENat.natCast_inj, exists_eq_left']; decide)]; norm_num [Set.encard_insert_of_notMem, Set.encard_singleton, hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, hH1j, hH1k, s2, s3, s4]
  -- 6. join 2, 5
  have s6a : ({a ∈ E | A ∈ G a}.ncard : ℤ) = 2 := s2
  have s6b : ({x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)}.ncard : ℤ) = 0 := by (have h := s5; simp only [← Set.Finite.cast_ncard_eq ((Set.finite_of_encard_eq_coe s5 : ({x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)} : Set α).Finite))] at h ⊢; exact_mod_cast h)
  exact ⟨by (have h := s6a; simp only [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s2; rw [h0] at h; exact ne_of_lt ((by norm_num : 0 < 2)) (by exact_mod_cast h)) : ({a ∈ E | A ∈ G a} : Set β).Finite))] at h ⊢; exact_mod_cast h), by (have h := s6b; simp only [← Set.Finite.cast_ncard_eq ((Set.finite_of_encard_eq_coe s5 : ({x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)} : Set α).Finite))] at h ⊢; exact_mod_cast h)⟩

end Parley.Tests.Notations.Graphs.ATriangleHasEvenDegrees
