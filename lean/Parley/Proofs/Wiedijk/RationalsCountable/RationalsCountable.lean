module

public import PowerTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.SchroederBernstein.SchroederBernstein

/-! Written from proofs/wiedijk/rationals-countable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RationalsCountable.RationalsCountable

theorem rationals_countable :
    (∃ g : ℤ → ℚ, Set.BijOn g {n : ℤ | 0 < n} (Set.univ : Set ℚ)) := by
  set f : ℤ → ℤ := fun n : ℤ => n with hD1
  set s : ℚ → ℤ := fun x : ℚ => (@ite _ (Rat.num x ≥ 0) (Classical.propDecidable (Rat.num x ≥ 0)) 0 1 : ℤ) with hD2
  -- 1. mun:function-into
  -- 2. proof
  have s2 : ∀ m : ℤ, 0 < m → (∀ n : ℤ, 0 < n → f m = f n → m = n) := by
    intro m hK2
    intro n hK3
    intro hA1
    -- 2.1. calculation
    calc m = f m := by simp (disch := omega) only [hD1]
      _ = f n := hA1
      _ = n := by simp (disch := omega) only [hD1]
  -- 3. def:one-to-one, from 1, 2
  have s3 : Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℚ) ∧ Set.InjOn f {n : ℤ | 0 < n} := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℚ)) (f := f) (Set.mapsTo_univ _ _))).mpr ⟨Set.mapsTo_univ _ _, by exact_mod_cast s2⟩
  -- 4. proof
  have s4 : ∀ x : ℚ, 0 ≤ s x ∧ Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := by
    intro x
    -- 4.1. membership, from D2
    have s4_1 : 0 ≤ s x := by rw [hD2]; split; norm_num; norm_num
    -- 4.2. axi:excluded-middle P := numer(x) ≥ 0
    have s4_2 : Rat.num x ≥ 0 ∨ ¬ Rat.num x ≥ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := 0 ≤ Rat.num x))
    -- 4.3. cases, from 4.2
    have s4_3 : Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := by
      rcases s4_2 with hC1 | hC2
      · skip
        -- 4.3.1. D2, from C1
        have s4_3_1 : s x = 0 := by simp (disch := omega) only [hD2, if_pos hC1]
        -- 4.3.2. def:abs x := numer(x), from C1
        have s4_3_2 : abs (Rat.num x) = Rat.num x := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := Rat.num x)) hC1
        -- 4.3.3. calculation
        calc Rat.num x = (1 - 2 * 0) * Rat.num x := by ring1
          _ = (1 - 2 * 0) * abs (Rat.num x) := congrArg (fun t : ℤ => (1 - 2 * 0) * t) s4_3_2.symm
          _ = (1 - 2 * s x) * abs (Rat.num x) := congrArg (fun t : ℤ => (1 - 2 * t) * abs (Rat.num x)) s4_3_1.symm
      · skip
        -- 4.3.4. D2, from C2
        have s4_3_4 : s x = 1 := by simp (disch := omega) only [hD2, if_neg hC2]
        -- 4.3.5. inequalities, from C2
        have s4_3_5 : Rat.num x < 0 := by linarith only [hC2]
        -- 4.3.6. def:abs x := numer(x), from 4.3.5
        have s4_3_6 : abs (Rat.num x) = -Rat.num x := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := Rat.num x)) s4_3_5
        -- 4.3.7. calculation
        calc Rat.num x = (1 - 2) * -Rat.num x := by ring1
          _ = (1 - 2) * abs (Rat.num x) := congrArg (fun t : ℤ => (1 - 2) * t) s4_3_6.symm
          _ = (1 - 2 * s x) * abs (Rat.num x) := by (have h := (congrArg (fun t : ℤ => (1 - 2 * t) * abs (Rat.num x)) s4_3_4).symm; push_cast [mul_one] at h ⊢; exact_mod_cast h)
    -- 4.4. join 4.1, 4.3
    have s4_4 : 0 ≤ s x ∧ Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := ⟨s4_1, s4_3⟩
    exact ⟨(s4_4).1, (s4_4).2⟩
  -- 5. membership
  have r101_2 : ∀ x : ℚ, 0 < (Rat.den x : ℤ) := by intro x; (exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := x)))
  have r101_3 : ∀ x : ℚ, 0 ≤ s x := by intro x; (exact (s4 x).1)
  have s5 : ∀ x : ℚ, ∃ m : ℤ, 0 < m ∧ (m : ℚ) = 2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x := by intro x; exact mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
  have hD3_kind : ∀ x : ℚ, ∃ m : ℤ, 0 < m ∧ (m : ℚ) = 2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x := by exact s5
  obtain ⟨g, hD3⟩ : ∃ g : ℚ → ℤ, ∀ x : ℚ, (g x : ℚ) = 2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x := ⟨fun x => (hD3_kind x).choose, fun x => (hD3_kind x).choose_spec⟩
  -- 6. membership, from D3
  have r111_2 : ∀ x : ℚ, 0 < (Rat.den x : ℤ) := by intro x; (exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := x)))
  have r111_3 : ∀ x : ℚ, 0 ≤ s x := by intro x; (exact (s4 x).1)
  have s6 : ∀ x : ℚ, 0 < g x := by intro x; exact by rw [hD3]; exact mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
  -- 7. mun:function-into, from 6
  have s7 : Set.MapsTo g (Set.univ : Set ℚ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.univ : Set ℚ)) (Y := {n : ℤ | 0 < n}) (by simpa only [Set.mem_univ, forall_const, Set.mem_ofPred_eq] using s6))
  -- 8. proof
  have s8 : ∀ x : ℚ, ∀ y : ℚ, g x = g y → x = y := by
    intro x
    intro y
    intro hA2
    -- 8.1. mun:lowest-terms-parts
    have s8_1a : 0 < (Rat.den x : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := x))
    have s8_1b : x = (Rat.num x : ℚ) / (Rat.den x : ℚ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_3 (x := x))
    -- 8.2. mun:lowest-terms-parts x := y
    have s8_2a : 0 < (Rat.den y : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := y))
    have s8_2b : y = (Rat.num y : ℚ) / (Rat.den y : ℚ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_3 (x := y))
    -- 8.3. instantiate x := x in line 4
    have s8_3 : 0 ≤ s x ∧ Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := by exact (s4 x)
    -- 8.4. instantiate x := y in line 4
    have s8_4 : 0 ≤ s y ∧ Rat.num y = (1 - 2 * s y) * abs (Rat.num y) := by exact (s4 y)
    -- 8.5. calculation
    have s8_5 : (2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x : ℚ) = 2 ^ abs (Rat.num y) * 3 ^ Rat.den y * 5 ^ s y := by
      calc (2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x : ℚ) = (g x : ℚ) := by simp (disch := omega) only [hD3]
        _ = (g y : ℚ) := by exact_mod_cast hA2
        _ = 2 ^ abs (Rat.num y) * 3 ^ Rat.den y * 5 ^ s y := by simp (disch := omega) only [hD3]
    -- 8.6. thm:prime-powers-unique a := |numer(x)|, b := denom(x), c := s(x), a′ := |numer(y)|, b′ := denom(y), c′ := s(y), from 8.3, 8.4, 8.5
    have r147_1 : 0 ≤ abs (Rat.num x) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_integer (z := Rat.num x))
    have r147_2 : 0 ≤ abs (Rat.num y) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_integer (z := Rat.num y))
    have r147_3 : 0 ≤ (Rat.den x : ℤ) := le_of_lt r101_2
    have r147_4 : 0 ≤ (Rat.den y : ℤ) := le_of_lt s8_2a
    have s8_6a : abs (Rat.num x) = abs (Rat.num y) := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_powers_unique_1 (a := abs (Rat.num x)) r147_1 (b := (Rat.den x : ℤ)) r147_3 (c := s x) s8_3.1 (a' := abs (Rat.num y)) r147_2 (b' := (Rat.den y : ℤ)) r147_4 (c' := s y) s8_4.1 (by (have h := s8_5; simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := r147_1), parley_zpow_toNat (n := (Rat.den x : ℤ)) (h := le_of_lt r101_2), parley_zpow_toNat (n := s x) (h := r101_3), parley_zpow_toNat (n := abs (Rat.num y)) (h := r147_2), parley_zpow_toNat (n := (Rat.den y : ℤ)) (h := le_of_lt s8_2a), parley_zpow_toNat (n := s y) (h := s8_4.1)] at h ⊢; exact_mod_cast h)))
    have s8_6b : (Rat.den x : ℤ) = (Rat.den y : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_powers_unique_2 (a := abs (Rat.num x)) r147_1 (b := (Rat.den x : ℤ)) r147_3 (c := s x) s8_3.1 (a' := abs (Rat.num y)) r147_2 (b' := (Rat.den y : ℤ)) r147_4 (c' := s y) s8_4.1 (by (have h := s8_5; simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := r147_1), parley_zpow_toNat (n := (Rat.den x : ℤ)) (h := le_of_lt r101_2), parley_zpow_toNat (n := s x) (h := r101_3), parley_zpow_toNat (n := abs (Rat.num y)) (h := r147_2), parley_zpow_toNat (n := (Rat.den y : ℤ)) (h := le_of_lt s8_2a), parley_zpow_toNat (n := s y) (h := s8_4.1)] at h ⊢; exact_mod_cast h)))
    have s8_6c : s x = s y := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_powers_unique_3 (a := abs (Rat.num x)) r147_1 (b := (Rat.den x : ℤ)) r147_3 (c := s x) s8_3.1 (a' := abs (Rat.num y)) r147_2 (b' := (Rat.den y : ℤ)) r147_4 (c' := s y) s8_4.1 (by (have h := s8_5; simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := r147_1), parley_zpow_toNat (n := (Rat.den x : ℤ)) (h := le_of_lt r101_2), parley_zpow_toNat (n := s x) (h := r101_3), parley_zpow_toNat (n := abs (Rat.num y)) (h := r147_2), parley_zpow_toNat (n := (Rat.den y : ℤ)) (h := le_of_lt s8_2a), parley_zpow_toNat (n := s y) (h := s8_4.1)] at h ⊢; exact_mod_cast h)))
    -- 8.7. calculation
    have s8_7 : Rat.num x = Rat.num y := by
      calc Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := s8_3.2
        _ = (1 - 2 * s y) * abs (Rat.num x) := congrArg (fun t : ℤ => (1 - 2 * t) * abs (Rat.num x)) s8_6c
        _ = (1 - 2 * s y) * abs (Rat.num y) := congrArg (fun t : ℤ => (1 - 2 * s y) * t) s8_6a
        _ = Rat.num y := s8_4.2.symm
    -- 8.8. calculation
    calc x = (Rat.num x : ℚ) / (Rat.den x : ℚ) := s8_1b
      _ = (Rat.num y : ℚ) / (Rat.den x : ℚ) := by
          have e_w : (Rat.num x : ℚ) = (Rat.num y : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s8_7; push_cast at h ⊢; linear_combination h
          exact congrArg (fun t : ℚ => t / (Rat.den x : ℚ)) e_w
      _ = (Rat.num y : ℚ) / (Rat.den y : ℚ) := by
          have e_w : (Rat.den x : ℚ) = (Rat.den y : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s8_6b; push_cast at h ⊢; linear_combination h
          exact congrArg (fun t : ℚ => (Rat.num y : ℚ) / t) e_w
      _ = y := s8_2b.symm
  -- 9. def:one-to-one, from 7, 8
  have s9 : Set.MapsTo g (Set.univ : Set ℚ) {n : ℤ | 0 < n} ∧ Set.InjOn g (Set.univ : Set ℚ) := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℚ)) (Y := {n : ℤ | 0 < n}) (f := g) s7)).mpr ⟨s7, by intro s _; exact s8 s⟩
  -- 10. thm:schroeder-bernstein A := ℕ, B := ℚ, from 3, 9
  exact (Parley.Proofs.Wiedijk.SchroederBernstein.SchroederBernstein.schroeder_bernstein (A := {n : ℤ | 0 < n}) (B := (Set.univ : Set ℚ)) (f := f) s3 (g := g) s9)

end Parley.Proofs.Wiedijk.RationalsCountable.RationalsCountable
