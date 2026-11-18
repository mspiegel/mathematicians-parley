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
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.RingNF
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
  set f : ℤ → ℚ := fun n : ℤ => (n : ℚ) with hD1
  set s : ℚ → ℤ := fun x : ℚ => (@ite _ (Rat.num x ≥ 0) (Classical.propDecidable (Rat.num x ≥ 0)) 0 1 : ℤ) with hD2
  set g : ℚ → ℚ := fun x : ℚ => (2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x : ℚ) with hD3
  -- 1. mun:function-into
  -- 2. proof
  have s2 : ∀ m : ℤ, 0 < m → (∀ n : ℤ, 0 < n → f m = f n → m = n) := by
    intro m hK2
    intro n hK3
    intro hA1
    -- 2.1. calculation
    qify
    calc (m : ℚ) = f m := by simp (disch := omega) only [hD1]
      _ = f n := hA1
      _ = (n : ℚ) := by simp (disch := omega) only [hD1]
  -- 3. def:one-to-one, from 1, 2
  have s3 : Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℚ) ∧ Set.InjOn f {n : ℤ | 0 < n} := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℚ)) (f := f) (Set.mapsTo_univ _ _))).mpr ⟨Set.mapsTo_univ _ _, by exact_mod_cast s2⟩
  -- 4. proof
  have s4 : ∀ x : ℚ, 0 ≤ s x ∧ Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := by
    intro x
    -- 4.1. membership, from D2
    have s4_1 : 0 ≤ s x := by simp only [hD2]; split; norm_num; norm_num
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
  -- 5. membership, from D3
  have r104_2 : ∀ x : ℚ, 0 < (Rat.den x : ℤ) := by intro x; (exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := x)))
  have r104_3 : ∀ x : ℚ, 0 ≤ s x := by intro x; (exact (s4 x).1)
  have s5 : ∀ x : ℚ, ∃ m : ℤ, 0 < m ∧ (m : ℚ) = g x := by intro x; rw [hD3]; exact ⟨2 ^ (abs (Rat.num x)).toNat * 3 ^ Rat.den x * 5 ^ (s x).toNat, mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _), by simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := abs_nonneg _), parley_zpow_toNat (n := s x) (h := r104_3 x)]; push_cast; ring⟩
  obtain ⟨g, s5_pos, s5_eq⟩ : ∃ g' : ℚ → ℤ, (∀ x : ℚ, 0 < g' x) ∧ (∀ x : ℚ, (g' x : ℚ) = g x) := ⟨fun x => (s5 x).choose, fun x => (s5 x).choose_spec.1, fun x => (s5 x).choose_spec.2⟩
  have hD3_g : ∀ x : ℚ, (g x : ℚ) = 2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x := fun x => (s5_eq x).trans (by simp only [hD3])
  -- 6. mun:function-into, from 5
  have s6 : Set.MapsTo g (Set.univ : Set ℚ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.univ : Set ℚ)) (Y := {n : ℤ | 0 < n}) (by simpa only [hD3, ge_iff_le, Set.mem_univ, forall_const, Set.mem_ofPred_eq] using s5_pos))
  -- 7. proof
  have s7 : ∀ x : ℚ, ∀ y : ℚ, g x = g y → x = y := by
    intro x
    intro y
    intro hA2
    -- 7.1. mun:lowest-terms-parts
    have s7_1a : 0 < (Rat.den x : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := x))
    have s7_1b : x = (Rat.num x : ℚ) / (Rat.den x : ℚ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_3 (x := x))
    -- 7.2. mun:lowest-terms-parts x := y
    have s7_2a : 0 < (Rat.den y : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_2 (x := y))
    have s7_2b : y = (Rat.num y : ℚ) / (Rat.den y : ℚ) := by exact (Parley.Items.Stdlib.Numbers.mun_lowest_terms_parts_3 (x := y))
    -- 7.3. instantiate x := x in line 4
    have s7_3 : 0 ≤ s x ∧ Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := by exact (s4 x)
    -- 7.4. instantiate x := y in line 4
    have s7_4 : 0 ≤ s y ∧ Rat.num y = (1 - 2 * s y) * abs (Rat.num y) := by exact (s4 y)
    -- 7.5. calculation
    have s7_5 : (2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x : ℚ) = 2 ^ abs (Rat.num y) * 3 ^ Rat.den y * 5 ^ s y := by
      calc (2 ^ abs (Rat.num x) * 3 ^ Rat.den x * 5 ^ s x : ℚ) = (g x : ℚ) := by simp (disch := omega) only [hD3_g]
        _ = (g y : ℚ) := by exact_mod_cast hA2
        _ = 2 ^ abs (Rat.num y) * 3 ^ Rat.den y * 5 ^ s y := by simp (disch := omega) only [hD3_g]
    -- 7.6. thm:prime-powers-unique a := |numer(x)|, b := denom(x), c := s(x), a′ := |numer(y)|, b′ := denom(y), c′ := s(y), from 7.3, 7.4, 7.5
    have r140_1 : 0 ≤ abs (Rat.num x) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_integer (z := Rat.num x))
    have r140_2 : 0 ≤ abs (Rat.num y) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_integer (z := Rat.num y))
    have r140_3 : 0 ≤ (Rat.den x : ℤ) := le_of_lt s7_1a
    have r140_4 : 0 ≤ (Rat.den y : ℤ) := le_of_lt s7_2a
    have s7_6a : abs (Rat.num x) = abs (Rat.num y) := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_powers_unique_1 (a := abs (Rat.num x)) r140_1 (b := (Rat.den x : ℤ)) r140_3 (c := s x) s7_3.1 (a' := abs (Rat.num y)) r140_2 (b' := (Rat.den y : ℤ)) r140_4 (c' := s y) s7_4.1 (by (have h := s7_5; simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := r140_1), parley_zpow_toNat (n := (Rat.den x : ℤ)) (h := le_of_lt s7_1a), parley_zpow_toNat (n := s x) (h := s7_3.1), parley_zpow_toNat (n := abs (Rat.num y)) (h := r140_2), parley_zpow_toNat (n := (Rat.den y : ℤ)) (h := le_of_lt s7_2a), parley_zpow_toNat (n := s y) (h := s7_4.1)] at h ⊢; exact_mod_cast h)))
    have s7_6b : (Rat.den x : ℤ) = (Rat.den y : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_powers_unique_2 (a := abs (Rat.num x)) r140_1 (b := (Rat.den x : ℤ)) r140_3 (c := s x) s7_3.1 (a' := abs (Rat.num y)) r140_2 (b' := (Rat.den y : ℤ)) r140_4 (c' := s y) s7_4.1 (by (have h := s7_5; simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := r140_1), parley_zpow_toNat (n := (Rat.den x : ℤ)) (h := le_of_lt s7_1a), parley_zpow_toNat (n := s x) (h := s7_3.1), parley_zpow_toNat (n := abs (Rat.num y)) (h := r140_2), parley_zpow_toNat (n := (Rat.den y : ℤ)) (h := le_of_lt s7_2a), parley_zpow_toNat (n := s y) (h := s7_4.1)] at h ⊢; exact_mod_cast h)))
    have s7_6c : s x = s y := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_powers_unique_3 (a := abs (Rat.num x)) r140_1 (b := (Rat.den x : ℤ)) r140_3 (c := s x) s7_3.1 (a' := abs (Rat.num y)) r140_2 (b' := (Rat.den y : ℤ)) r140_4 (c' := s y) s7_4.1 (by (have h := s7_5; simp only [parley_zpow_toNat (n := abs (Rat.num x)) (h := r140_1), parley_zpow_toNat (n := (Rat.den x : ℤ)) (h := le_of_lt s7_1a), parley_zpow_toNat (n := s x) (h := s7_3.1), parley_zpow_toNat (n := abs (Rat.num y)) (h := r140_2), parley_zpow_toNat (n := (Rat.den y : ℤ)) (h := le_of_lt s7_2a), parley_zpow_toNat (n := s y) (h := s7_4.1)] at h ⊢; exact_mod_cast h)))
    -- 7.7. calculation
    have s7_7 : Rat.num x = Rat.num y := by
      calc Rat.num x = (1 - 2 * s x) * abs (Rat.num x) := s7_3.2
        _ = (1 - 2 * s y) * abs (Rat.num x) := congrArg (fun t : ℤ => (1 - 2 * t) * abs (Rat.num x)) s7_6c
        _ = (1 - 2 * s y) * abs (Rat.num y) := congrArg (fun t : ℤ => (1 - 2 * s y) * t) s7_6a
        _ = Rat.num y := s7_4.2.symm
    -- 7.8. calculation
    calc x = (Rat.num x : ℚ) / (Rat.den x : ℚ) := s7_1b
      _ = (Rat.num y : ℚ) / (Rat.den x : ℚ) := by
          have e_w : (Rat.num x : ℚ) = (Rat.num y : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s7_7; push_cast at h ⊢; linear_combination h
          exact congrArg (fun t : ℚ => t / (Rat.den x : ℚ)) e_w
      _ = (Rat.num y : ℚ) / (Rat.den y : ℚ) := by
          have e_w : (Rat.den x : ℚ) = (Rat.den y : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s7_6b; push_cast at h ⊢; linear_combination h
          exact congrArg (fun t : ℚ => (Rat.num y : ℚ) / t) e_w
      _ = y := s7_2b.symm
  -- 8. def:one-to-one, from 6, 7
  have s8 : Set.MapsTo g (Set.univ : Set ℚ) {n : ℤ | 0 < n} ∧ Set.InjOn g (Set.univ : Set ℚ) := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℚ)) (Y := {n : ℤ | 0 < n}) (f := g) s6)).mpr ⟨s6, by intro s _ t _; exact s7 s t⟩
  -- 9. thm:schroeder-bernstein A := ℕ, B := ℚ, from 3, 8
  have hI : ∃ g : ℤ → ℚ, Set.BijOn g {n : ℤ | 0 < n} (Set.univ : Set ℚ) := by exact ((Parley.Proofs.Wiedijk.SchroederBernstein.SchroederBernstein.schroeder_bernstein (A := {n : ℤ | 0 < n}) (B := (Set.univ : Set ℚ)) (f := f) s3 (g := g) s8))
  exact hI

end Parley.Proofs.Wiedijk.RationalsCountable.RationalsCountable
