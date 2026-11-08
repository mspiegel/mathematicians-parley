module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/euler.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Euler.Euler

set_option maxHeartbeats 1000000 in
theorem euler (n : ℤ) (hH1 : 0 < n) (a : ℤ) (hH3 : (Int.gcd a n : ℤ) = 1) :
    a ^ Nat.totient n.toNat ≡ (1 : ℤ) [ZMOD n] := by
  set S : Set ℤ := {r ∈ (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) | (Int.gcd r n : ℤ) = 1} with hD1
  have hD1_finite : S.Finite := by rw [hD1]; exact (Set.finite_Icc _ _).subset (fun _ h => h.1)
  set f : ℤ → ℤ := fun r => r * a % n with hD2
  -- 1. mun:range-finite
  have s1 : (Set.Icc (0 : ℤ) (n - 1) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (0 : ℤ)) (b := n - 1))
  -- 2. mun:range-in-integers
  have s2 : (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_in_integers (a := (0 : ℤ)) (b := n - 1))
  -- 3. mun:set-builder-subset, from D1
  have s3 : S ⊆ (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ))) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ))) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ))); parley_set_side)
  -- 4. mun:finite-part, from 1, 3
  have s4 : S.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (Y := S) (by parley_whole_side) (by parley_whole_side))
  -- 5. mun:subset-transitive, from 2, 3
  have s5 : S ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (Z := (Set.univ : Set ℤ)) (by parley_whole_side) (by parley_whole_side))
  -- 6. proof
  have s6 : ∀ r ∈ S, f r ∈ S := by
    intro r hK1
    -- 6.1. def:set-builder u := r, from D1, K1
    have s6_1a : r ∈ Finset.Icc (0 : ℤ) (n - 1) := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).1 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).1 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).1; parley_set_side)
    have s6_1b : (Int.gcd r n : ℤ) = 1 := by
      try simp only [hD1] at *
      try push_cast at *
      first | linear_combination (norm := parley_norm) (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2 | exact_mod_cast ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2).symm | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2; rify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2; qify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2; parley_int_power h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK1).2; parley_set_side)
    -- 6.2. calculation
    have s6_2 : (Int.gcd (r * a % n) n : ℤ) = 1 := by
      calc (Int.gcd (r * a % n) n : ℤ) = (Int.gcd (r * a) n : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r * a) (b := n) (by parley_set_side))
        _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := r) (y := a) (n := n) (by parley_set_side) s6_1b hH3)
    -- 6.3. mun:mod-less
    have s6_3 : r * a % n < n := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := r * a) (b := n) (by parley_set_side))
    -- 6.4. mun:range-from-bounds, from 6.3
    have r80_2 : 0 ≤ r * a % n := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := r * a) (b := n) (by parley_set_side))
    have s6_4 : r * a % n ∈ Finset.Icc (0 : ℤ) (n - 1) := by exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_set_side) (x := r * a % n) (by parley_set_side) s6_3)
    -- 6.5. def:set-builder u := (r·a) mod n, from D1, 6.2, 6.4
    have s6_5 : r * a % n ∈ S := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r * a % n))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r * a % n))).mpr (by parley_set_side); parley_set_side)
    -- 6.6. D2, from K1
    have s6_6 : f r = r * a % n := by simp (disch := omega) only [hD2]
    -- 6.7. substitute f(r) = (r·a) mod n (line 6.6) into line 6.5
    parley_subst_at s6_6 s6_5
  -- 7. proof
  have s7 : ∀ s ∈ S, ∀ t ∈ S, f s = f t → s = t := by
    intro s hK2
    intro t hK3
    intro hK4
    -- 7.1. def:set-builder u := s, from D1, K2
    have s7_1a : s ∈ Finset.Icc (0 : ℤ) (n - 1) := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).1 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).1 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).1; parley_set_side)
    have s7_1b : (Int.gcd s n : ℤ) = 1 := by
      try simp only [hD1] at *
      try push_cast at *
      first | linear_combination (norm := parley_norm) (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2 | exact_mod_cast ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2).symm | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2; rify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2; qify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2; parley_int_power h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := s))).mp hK2).2; parley_set_side)
    -- 7.2. def:set-builder u := t, from D1, K3
    have s7_2a : t ∈ Finset.Icc (0 : ℤ) (n - 1) := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).1 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).1 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).1; parley_set_side)
    have s7_2b : (Int.gcd t n : ℤ) = 1 := by
      try simp only [hD1] at *
      try push_cast at *
      first | linear_combination (norm := parley_norm) (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2 | exact_mod_cast ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2).symm | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2; rify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2; qify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2; parley_int_power h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := t))).mp hK3).2; parley_set_side)
    -- 7.3. D2, from K2
    have s7_3 : f s = s * a % n := by simp (disch := omega) only [hD2]
    -- 7.4. D2, from K3
    have s7_4 : f t = t * a % n := by simp (disch := omega) only [hD2]
    -- 7.5. calculation
    have s7_5 : s * a % n = t * a % n := by
      calc s * a % n = f s := by parley_set_side
        _ = f t := by parley_set_side
        _ = t * a % n := by parley_set_side
    -- 7.6. mun:mod-equal-congruent, from 7.5
    have s7_6 : s * a ≡ t * a [ZMOD n] := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := s * a) (y := t * a) (n := n) (by parley_set_side) s7_5)
    -- 7.7. thm:congruent-cancel c := a, from H3, 7.6
    have s7_7 : s ≡ t [ZMOD n] := by exact (Parley.Items.Stdlib.Divisibility.thm_congruent_cancel (x := s) (y := t) (c := a) (n := n) (by parley_set_side) s7_6 hH3)
    -- 7.8. mun:congruent-in-range, from 7.1, 7.2, 7.7
    exact (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_set_side) (x := s) s7_1a (y := t) s7_2a s7_7)
  -- 8. mun:function-into, from 6
  have s8 : Set.MapsTo f S S := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := S) (Y := S) (by parley_set_side) (by simpa using s6))
  -- 9. def:one-to-one, from 7, 8
  have s9 : Set.MapsTo f S S ∧ Set.InjOn f S := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := S) (Y := S) (f := f) (by parley_set_side))).mpr (by parley_set_side)
  -- 10. thm:product-reorder, from 4, 5, 9
  have s10 : (∏ᶠ r ∈ S, (f r : ℤ)) = (∏ᶠ r ∈ S, (r : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9) | (have h := (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9) | exact_mod_cast ((Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9)).symm | (have h := (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_reorder (X := S) (f := f) s5 s4 s9); parley_set_side)
  -- 11. proof
  have s11 : ∀ r ∈ S, r * a ≡ f r [ZMOD n] := by
    intro r hK5
    -- 11.1. def:set-builder u := r, from D1, K5
    have s11_1a : r ∈ Finset.Icc (0 : ℤ) (n - 1) := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).1 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).1 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).1; parley_set_side)
    have s11_1b : (Int.gcd r n : ℤ) = 1 := by
      try simp only [hD1] at *
      try push_cast at *
      first | linear_combination (norm := parley_norm) (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2 | exact_mod_cast ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2).symm | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2; rify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2; qify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2; parley_int_power h) | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp hK5).2; parley_set_side)
    -- 11.2. mun:mod-congruent
    have s11_2 : r * a ≡ r * a % n [ZMOD n] := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := r * a) (n := n) (by parley_set_side))
    -- 11.3. D2, from K5
    have s11_3 : f r = r * a % n := by simp (disch := omega) only [hD2]
    -- 11.4. substitute f(r) = (r·a) mod n (line 11.3) into line 11.2
    parley_subst_at s11_3 s11_2
  -- 12. thm:product-congruent X := S, from 4, 5, 11
  have r160_1 : Set.MapsTo f S S := by parley_set_side
  have s12 : (∏ᶠ r ∈ S, (r * a : ℤ)) ≡ (∏ᶠ r ∈ S, (f r : ℤ)) [ZMOD n] := by first | exact (Parley.Items.Stdlib.Divisibility.thm_product_congruent (f := f) (X := S) s5 s4 (c := a) (n := n) (by parley_set_side) (by simpa using s11) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Divisibility.thm_product_congruent (f := f) (X := S) s5 s4 (c := a) (n := n) (by parley_set_side) (by simpa using s11) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_product_congruent (f := f) (X := S) s5 s4 (c := a) (n := n) (by parley_set_side) (by simpa using s11) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_product_congruent (f := f) (X := S) s5 s4 (c := a) (n := n) (by parley_set_side) (by simpa using s11) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_product_congruent (f := f) (X := S) s5 s4 (c := a) (n := n) (by parley_set_side) (by simpa using s11) (by parley_set_side)); parley_set_side)
  -- 13. def:φ, from D1
  have s13 : (Nat.totient n.toNat : ℤ) = (S.ncard : ℤ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.def_phi (n := n) (by parley_set_side)); parley_set_side)
  -- 14. substitute
  have s14 : a ^ S.ncard * (∏ᶠ r ∈ S, (r : ℤ)) ≡ (∏ᶠ r ∈ S, (f r : ℤ)) [ZMOD n] := by
    have c1 : (∏ᶠ r ∈ S, (r * a : ℤ)) = a ^ S.ncard * (∏ᶠ r ∈ S, (r : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a))) | exact_mod_cast (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a))).symm | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.thm_product_factor (X := S) s5 s4 (c := a)); parley_set_side)
    have row1 : a ^ S.ncard * (∏ᶠ r ∈ S, (r : ℤ)) ≡ (∏ᶠ r ∈ S, (f r : ℤ)) [ZMOD n] := by parley_subst_at c1 s12
    exact row1
  -- 15. substitute ∏(r ∈ S) f(r) = ∏(r ∈ S) r (line 10) into line 14
  have s15 : a ^ S.ncard * (∏ᶠ r ∈ S, (r : ℤ)) ≡ (∏ᶠ r ∈ S, (r : ℤ)) [ZMOD n] := by parley_subst_at s10 s14
  -- 16. substitute φ(n) = |S| (line 13) into line 15
  have s16 : a ^ Nat.totient n.toNat * (∏ᶠ r ∈ S, (r : ℤ)) ≡ (∏ᶠ r ∈ S, (r : ℤ)) [ZMOD n] := by first | parley_subst_at s13 s15 | (have e_nat : Nat.totient n.toNat = S.ncard := by exact_mod_cast s13; parley_subst_at e_nat s15)
  -- 17. def:set-builder u := r, from D1
  have s17 : ∀ r ∈ S, (Int.gcd r n : ℤ) = 1 := by
    intro r h_r
    try simp only [hD1] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side)).symm | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun r : ℤ => (Int.gcd r n : ℤ) = 1)) (X := (Set.Icc (0 : ℤ) (n - 1) : Set ℤ)) (u := r))).mp (by parley_set_side); parley_set_side)
  -- 18. thm:product-coprime, from 4, 5, 17
  have s18 : (Int.gcd (∏ᶠ r ∈ S, (r : ℤ)) n : ℤ) = 1 := (Parley.Items.Stdlib.Divisibility.thm_product_coprime (X := S) s5 s4 (n := n) (by parley_set_side) s17)
  -- 19. def:congruent-mod, from 16
  have r184_1 : 0 < (Nat.totient n.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_phi_natural (n := n) (by parley_set_side))
  have s19 : n ∣ a ^ Nat.totient n.toNat * (∏ᶠ r ∈ S, (r : ℤ)) - (∏ᶠ r ∈ S, (r : ℤ)) := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a ^ Nat.totient n.toNat * (∏ᶠ r ∈ S, (r : ℤ))) (b := ∏ᶠ r ∈ S, (r : ℤ)))).mp s16
  -- 20. substitute
  have r189_1 : 0 < (Nat.totient n.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_phi_natural (n := n) (by parley_set_side))
  have s20 : n ∣ (a ^ Nat.totient n.toNat - 1) * (∏ᶠ r ∈ S, (r : ℤ)) := by
    have c1 : a ^ Nat.totient n.toNat * (∏ᶠ r ∈ S, (r : ℤ)) - (∏ᶠ r ∈ S, (r : ℤ)) = (a ^ Nat.totient n.toNat - 1) * (∏ᶠ r ∈ S, (r : ℤ)) := by parley_ring
    have row1 : n ∣ (a ^ Nat.totient n.toNat - 1) * (∏ᶠ r ∈ S, (r : ℤ)) := by parley_subst_at c1 s19
    exact row1
  -- 21. thm:coprime-divides c := ∏(r ∈ S) r, from 18, 20
  have r196_2 : 0 < (Nat.totient n.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_phi_natural (n := n) (by parley_set_side))
  have s21 : n ∣ a ^ Nat.totient n.toNat - 1 := by exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := a ^ Nat.totient n.toNat - 1) (c := ∏ᶠ r ∈ S, (r : ℤ)) (n := n) (by parley_set_side) s20 s18)
  -- 22. def:congruent-mod, from 21
  have r201_1 : 0 < (Nat.totient n.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_phi_natural (n := n) (by parley_set_side))
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a ^ Nat.totient n.toNat) (b := (1 : ℤ)))).mpr s21

end Parley.Proofs.Wiedijk.Euler.Euler
