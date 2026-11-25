module

public import PowerTactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Parley.Items.Proofs.Wiedijk.PythagoreanTriples
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Wiedijk.PythagoreanTriples.EvenLeg
public import Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple
public import Parley.Proofs.Wiedijk.PythagoreanTriples.TripleScaled

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.TripleParameters

theorem triple_parameters (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : a ^ 2 + b ^ 2 = c ^ 2) :
    (∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = k * (m ^ 2 + n ^ 2) ∧ ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ))))) := by
  -- 1. obtain k: thm:triple-scaled, from H4
  obtain ⟨k, s1a, ⟨⟨⟨⟨s1b, s1c⟩, s1d⟩, s1e⟩, s1f⟩⟩ := (Parley.Proofs.Wiedijk.PythagoreanTriples.TripleScaled.triple_scaled (a := a) hH1 (b := b) hH2 (c := c) hH3 hH4)
  -- 2. thm:even-leg a := a/k, b := b/k, c := c/k, from 1
  have s2 : (∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) ∧ Even m) ∨ (∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) ∧ Even m) := by
    have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1b; exact ⟨m, by exact_mod_cast hm⟩
    have whole2 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1c; exact ⟨m, by exact_mod_cast hm⟩
    have s1e := parley_witness_at (parley_witness_at s1e (Classical.choose whole1 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))) (Classical.choose whole2 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))
    have named_claim : Even (Classical.choose whole1 : ℤ) ∨ Even (Classical.choose whole2 : ℤ) := by exact (Parley.Proofs.Wiedijk.PythagoreanTriples.EvenLeg.even_leg (a := (Classical.choose whole1 : ℤ)) (by obtain ⟨w, hw0, hw⟩ := s1b; have e : Classical.choose whole1 = w := Int.cast_injective ((Classical.choose_spec whole1).trans hw.symm); omega) (b := (Classical.choose whole2 : ℤ)) (by obtain ⟨w, hw0, hw⟩ := s1c; have e : Classical.choose whole2 = w := Int.cast_injective ((Classical.choose_spec whole2).trans hw.symm); omega) (c := (Classical.choose s1d)) (by linarith only [(Classical.choose_spec s1d).1]) (by (have h := s1f; rw [← (Classical.choose_spec s1d).2, ← Classical.choose_spec whole1, ← Classical.choose_spec whole2] at h; exact_mod_cast h)))
    exact Or.imp (fun h => ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]), h⟩) (fun h => ⟨(Classical.choose whole2 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]), h⟩) named_claim
  -- 3. cases, from 2
  have s3 : ∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = k * (m ^ 2 + n ^ 2) ∧ ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ)))) := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. obtain m, n: thm:primitive-triple a := a/k, b := b/k, c := c/k, from C1, 1
      obtain ⟨m, s3_1a, n, s3_1b, ⟨⟨⟨⟨⟨s3_1c, s3_1d⟩, s3_1e⟩, s3_1f⟩, s3_1g⟩, s3_1h⟩⟩ := (Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple.primitive_triple (a := (Classical.choose s1b)) (by linarith only [(Classical.choose_spec s1b).1]) (b := (Classical.choose s1c)) (by linarith only [(Classical.choose_spec s1c).1]) (c := (Classical.choose s1d)) (by linarith only [(Classical.choose_spec s1d).1]) (by (have h := s1f; rw [← (Classical.choose_spec s1d).2, ← (Classical.choose_spec s1b).2, ← (Classical.choose_spec s1c).2] at h; exact_mod_cast h)) (parley_witness_at (parley_witness_at s1e (Classical.choose s1b) (Classical.choose_spec s1b).2) (Classical.choose s1c) (Classical.choose_spec s1c).2) (parley_witness_at hC1 (Classical.choose s1b) (Classical.choose_spec s1b).2))
      replace s3_1f : (a : ℚ) / (k : ℚ) = 2 * (m : ℚ) * (n : ℚ) := by rw [← (Classical.choose_spec s1b).2]; exact_mod_cast s3_1f
      replace s3_1g : (b : ℚ) / (k : ℚ) = (m : ℚ) ^ 2 - (n : ℚ) ^ 2 := by rw [← (Classical.choose_spec s1c).2]; exact_mod_cast s3_1g
      replace s3_1h : (c : ℚ) / (k : ℚ) = (m : ℚ) ^ 2 + (n : ℚ) ^ 2 := by rw [← (Classical.choose_spec s1d).2]; exact_mod_cast s3_1h
      -- 3.2. algebra, from 3.1
      have s3_2 : a = 2 * k * m * n := by qify at *; have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((k : ℚ)) * s3_1f
      -- 3.3. algebra, from 3.1
      have s3_3 : b = k * (m ^ 2 - n ^ 2) := by qify at *; have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((k : ℚ)) * s3_1g
      -- 3.4. algebra, from 3.1
      have s3_4 : c = k * (m ^ 2 + n ^ 2) := by qify at *; have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((k : ℚ)) * s3_1h
      -- 3.5. calculation
      have s3_5 : ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ) := by
        (have h := (by
          calc ({a, b} : Set ℤ) = ({2 * k * m * n, b} : Set ℤ) := congrArg (fun t : ℤ => ({t, b} : Set ℤ)) s3_2
            _ = ({2 * k * m * n, k * (m ^ 2 - n ^ 2)} : Set ℤ) := congrArg (fun t : ℤ => ({2 * k * m * n, t} : Set ℤ)) s3_3); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto)
      -- 3.6. exhibit, from 3.4, 3.5
      exact ⟨k, s1a, m, s3_1a, n, s3_1b, ⟨s3_4, s3_5⟩⟩
    · skip
      -- 3.7. mun:gcd-commutes a := b/k, b := a/k
      have r657_1 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1c; exact ⟨m, by exact_mod_cast hm⟩
        exact ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1])⟩
      have r657_2 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1b; exact ⟨m, by exact_mod_cast hm⟩
        exact ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1])⟩
      have s3_7 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) ∧ (∃ m₀ : ℤ, (m₀ : ℚ) = (a : ℚ) / (k : ℚ) ∧ (Int.gcd m m₀ : ℤ) = (Int.gcd m₀ m : ℤ)) := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) := by obtain ⟨m, hm⟩ := r657_1; exact ⟨m, by exact_mod_cast hm⟩
        have whole2 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) := by obtain ⟨m, hm⟩ := r657_2; exact ⟨m, by exact_mod_cast hm⟩
        refine ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]), (Classical.choose whole2 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]), ?_⟩
        (exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (Classical.choose whole1 : ℤ)) (b := (Classical.choose whole2 : ℤ))))
      -- 3.8. calculation
      have s3_8 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) ∧ (∃ m₀ : ℤ, (m₀ : ℚ) = (a : ℚ) / (k : ℚ) ∧ (Int.gcd m m₀ : ℤ) = 1) := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1c; exact ⟨m, by exact_mod_cast hm⟩
        have whole2 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1b; exact ⟨m, by exact_mod_cast hm⟩
        have s3_7 := parley_witness_at (parley_witness_at s3_7 (Classical.choose whole1 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))) (Classical.choose whole2 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))
        have s1e := parley_witness_at (parley_witness_at s1e (Classical.choose whole2 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))) (Classical.choose whole1 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))
        refine ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]), (Classical.choose whole2 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]), ?_⟩
        exact (by
          calc (Int.gcd (Classical.choose whole1 : ℤ) (Classical.choose whole2 : ℤ) : ℤ) = (Int.gcd (Classical.choose whole2 : ℤ) (Classical.choose whole1 : ℤ) : ℤ) := s3_7
            _ = 1 := s1e)
      -- 3.9. algebra, from 1
      have s3_9 : ((b : ℚ) / (k : ℚ)) ^ 2 + ((a : ℚ) / (k : ℚ)) ^ 2 = ((c : ℚ) / (k : ℚ)) ^ 2 := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1b; exact ⟨m, by exact_mod_cast hm⟩
        have whole2 : ∃ m : ℤ, (m : ℚ) = (b : ℚ) / (k : ℚ) := by obtain ⟨m, _, hm⟩ := s1c; exact ⟨m, by exact_mod_cast hm⟩
        have s1e := parley_witness_at (parley_witness_at s1e (Classical.choose whole1 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))) (Classical.choose whole2 : ℤ) (by (push_cast; simp only [Classical.choose_spec whole1, Classical.choose_spec whole2]))
        have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) s1f
      -- 3.10. obtain m, n: thm:primitive-triple a := b/k, b := a/k, c := c/k, from C2, 1, 3.8, 3.9
      obtain ⟨m, s3_10a, n, s3_10b, ⟨⟨⟨⟨⟨s3_10c, s3_10d⟩, s3_10e⟩, s3_10f⟩, s3_10g⟩, s3_10h⟩⟩ := (Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple.primitive_triple (a := (Classical.choose s1c)) (by linarith only [(Classical.choose_spec s1c).1]) (b := (Classical.choose s1b)) (by linarith only [(Classical.choose_spec s1b).1]) (c := (Classical.choose s1d)) (by linarith only [(Classical.choose_spec s1d).1]) (by (have h := s3_9; rw [← (Classical.choose_spec s1d).2, ← (Classical.choose_spec s1c).2, ← (Classical.choose_spec s1b).2] at h; exact_mod_cast h)) (parley_witness_at (parley_witness_at s3_8 (Classical.choose s1c) (Classical.choose_spec s1c).2) (Classical.choose s1b) (Classical.choose_spec s1b).2) (parley_witness_at hC2 (Classical.choose s1c) (Classical.choose_spec s1c).2))
      replace s3_10f : (b : ℚ) / (k : ℚ) = 2 * (m : ℚ) * (n : ℚ) := by rw [← (Classical.choose_spec s1c).2]; exact_mod_cast s3_10f
      replace s3_10g : (a : ℚ) / (k : ℚ) = (m : ℚ) ^ 2 - (n : ℚ) ^ 2 := by rw [← (Classical.choose_spec s1b).2]; exact_mod_cast s3_10g
      replace s3_10h : (c : ℚ) / (k : ℚ) = (m : ℚ) ^ 2 + (n : ℚ) ^ 2 := by rw [← (Classical.choose_spec s1d).2]; exact_mod_cast s3_10h
      -- 3.11. algebra, from 3.10
      have s3_11 : a = k * (m ^ 2 - n ^ 2) := by qify at *; have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((k : ℚ)) * s3_10g
      -- 3.12. algebra, from 3.10
      have s3_12 : b = 2 * k * m * n := by qify at *; have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((k : ℚ)) * s3_10f
      -- 3.13. algebra, from 3.10
      have s3_13 : c = k * (m ^ 2 + n ^ 2) := by qify at *; have hz1 : (k : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((k : ℚ)) * s3_10h
      -- 3.14. calculation
      have s3_14 : ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ) := by
        calc ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), b} : Set ℤ) := congrArg (fun t : ℤ => ({t, b} : Set ℤ)) s3_11
          _ = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ) := congrArg (fun t : ℤ => ({k * (m ^ 2 - n ^ 2), t} : Set ℤ)) s3_12
      -- 3.15. exhibit, from 3.13, 3.14
      exact ⟨k, s1a, m, s3_10a, n, s3_10b, ⟨s3_13, s3_14⟩⟩
  -- 4. D0, from 3
  exact s3

end Parley.Proofs.Wiedijk.PythagoreanTriples.TripleParameters
