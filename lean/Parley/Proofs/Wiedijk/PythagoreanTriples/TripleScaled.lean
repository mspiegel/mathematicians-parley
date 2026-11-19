module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.TripleScaled

theorem triple_scaled (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : a ^ 2 + b ^ 2 = c ^ 2) :
    (∃ k : ℤ, 0 < k ∧ (((((∃ m : ℤ, 0 < m ∧ (m : ℚ) = (a : ℚ) / (k : ℚ)) ∧ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = (b : ℚ) / (k : ℚ))) ∧ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = (c : ℚ) / (k : ℚ))) ∧ (∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) ∧ (∃ m₀ : ℤ, (m₀ : ℚ) = (b : ℚ) / (k : ℚ) ∧ (Int.gcd m m₀ : ℤ) = 1))) ∧ ((a : ℚ) / (k : ℚ)) ^ 2 + ((b : ℚ) / (k : ℚ)) ^ 2 = ((c : ℚ) / (k : ℚ)) ^ 2)) := by
  have hD1_kind : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) hH1 (b := b) hH2)
  set k : ℤ := (Int.gcd a b : ℤ) with hD1
  have hD1_pos := hD1_kind
  -- 1. def:gcd, from D1
  have s1a : k ∣ a := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) hH1 (b := b) hH2); push_cast at h; exact h)
  have s1b : k ∣ b := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) hH1 (b := b) hH2); push_cast at h; exact h)
  -- 2. mun:divides-quotient n := a, d := k, from 1
  have s2 : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = (a : ℚ) / (k : ℚ) := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := a) hH1 (d := k) hD1_pos)).mp s1a
  -- 3. mun:divides-quotient n := b, d := k, from 1
  have s3 : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = (b : ℚ) / (k : ℚ) := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := b) hH2 (d := k) hD1_pos)).mp s1b
  -- 4. mun:divides-square d := k, n := a, from 1
  have s4 : k ^ 2 ∣ a ^ 2 := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_square (d := k) (n := a))).mp s1a
  -- 5. mun:divides-square d := k, n := b, from 1
  have s5 : k ^ 2 ∣ b ^ 2 := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_square (d := k) (n := b))).mp s1b
  -- 6. mun:divides-sum d := k², a := a², b := b², from 4, 5
  have s6 : k ^ 2 ∣ a ^ 2 + b ^ 2 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := k ^ 2) (a := a ^ 2) (b := b ^ 2) s4 s5)
  -- 7. substitute a² + b² = c² (H4) into line 6
  have s7 : k ^ 2 ∣ c ^ 2 := Eq.subst (motive := (fun t : ℤ => k ^ 2 ∣ t)) hH4 s6
  -- 8. mun:divides-square d := k, n := c, from 7
  have s8 : k ∣ c := ((Parley.Items.Stdlib.Divisibility.mun_divides_square (d := k) (n := c))).mpr s7
  -- 9. mun:divides-quotient n := c, d := k, from 8
  have s9 : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = (c : ℚ) / (k : ℚ) := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := c) hH3 (d := k) hD1_pos)).mp s8
  -- 10. mun:gcd-quotients-coprime, from D1
  have r552_1 : b ≠ 0 := hH2.ne'
  have s10 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) / (k : ℚ) ∧ (∃ m₀ : ℤ, (m₀ : ℚ) = (b : ℚ) / (k : ℚ) ∧ (Int.gcd m m₀ : ℤ) = 1) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_quotients_coprime (a := a) (b := b) r552_1); push_cast at h ⊢; exact h)
  -- 11. algebra
  have s11 : ((a : ℚ) / (k : ℚ)) ^ 2 + ((b : ℚ) / (k : ℚ)) ^ 2 = ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / (k : ℚ) ^ 2 := by have hz1 : (k : ℚ) ≠ 0 := (by positivity); field
  -- 12. substitute a² + b² = c² (H4) into line 11
  have s12 : ((a : ℚ) / (k : ℚ)) ^ 2 + ((b : ℚ) / (k : ℚ)) ^ 2 = (c : ℚ) ^ 2 / (k : ℚ) ^ 2 := by
    have e_w : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 = (c : ℚ) ^ 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hH4; push_cast at h; linear_combination h
    exact Eq.subst (motive := (fun t : ℚ => ((a : ℚ) / (k : ℚ)) ^ 2 + ((b : ℚ) / (k : ℚ)) ^ 2 = t / (k : ℚ) ^ 2)) e_w s11
  -- 13. calculation
  have s13 : ((a : ℚ) / (k : ℚ)) ^ 2 + ((b : ℚ) / (k : ℚ)) ^ 2 = ((c : ℚ) / (k : ℚ)) ^ 2 := by
    calc ((a : ℚ) / (k : ℚ)) ^ 2 + ((b : ℚ) / (k : ℚ)) ^ 2 = (c : ℚ) ^ 2 / (k : ℚ) ^ 2 := s12
      _ = ((c : ℚ) / (k : ℚ)) ^ 2 := by have hz1 : (k : ℚ) ≠ 0 := (by positivity); field
  -- 14. exhibit, from 2, 3, 9, 10, 13
  exact ⟨k, hD1_pos, ⟨⟨⟨⟨s2, s3⟩, s9⟩, s10⟩, s13⟩⟩

end Parley.Proofs.Wiedijk.PythagoreanTriples.TripleScaled
