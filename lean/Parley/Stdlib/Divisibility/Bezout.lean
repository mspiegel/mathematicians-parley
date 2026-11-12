module

public import AlgebraTactics
public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Stdlib.Divisibility.LeastCombinationDivides

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.Bezout

theorem bezout (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    (∃ x : ℤ, ∃ y : ℤ, a * x + b * y = (Int.gcd a b : ℤ)) := by
  set S : Set ℤ := {t : ℤ | 0 < t ∧ (∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)} with hD1
  -- 1. algebra
  have s1 : b = a * 0 + b * 1 := by parley_ring
  -- 2. def:set-builder u := b, from D1, 1
  have s2 : b ∈ S := by
    have hI : b ∈ {c : ℤ | 0 < c ∧ (∃ d : ℤ, ∃ e : ℤ, c = a * d + b * e)} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := b))).mpr ⟨by parley_set_side, (0 : ℤ), (1 : ℤ), s1⟩)
    exact hI
  -- 3. mun:set-builder-subset, from D1
  have s3 : S ⊆ {n : ℤ | 0 < n} := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    have hI : {c : ℤ | 0 < c ∧ (∃ d : ℤ, ∃ e : ℤ, c = a * d + b * e)} ⊆ {n : ℤ | 0 < n} := by parley_instance ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n})))
    exact hI
  -- 4. obtain d: axi:well-ordering, from 2, 3
  obtain ⟨d, s4a, s4b⟩ := (Parley.Items.Stdlib.Numbers.axi_well_ordering (S := S) s3 (by parley_set_side))
  -- 5. def:subset, from 3
  have s5 : ∀ t ∈ S, 0 < t := by
    have hI : ∀ t ∈ S, 0 < t := by parley_instance (((Parley.Items.Stdlib.Sets.def_subset (X := S) (Y := {n : ℤ | 0 < n}))).mp s3)
    exact hI
  -- 6. instantiate t := d in line 5, from 4
  have s6 : 0 < d := by exact (s5 d s4a)
  -- 7. obtain x₀, y₀: def:set-builder u := d, from D1, 4
  obtain ⟨_, x₀, y₀, s7⟩ := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := d))).mp (by parley_set_side)
  -- 8. proof
  have s8 : ∀ x : ℤ, ∀ y : ℤ, 0 < a * x + b * y → d ≤ a * x + b * y := by
    intro x
    intro y
    intro hK3
    -- 8.1. def:set-builder u := a·x + b·y, from D1, K3
    have s8_1 : a * x + b * y ∈ S := by
      have hI : a * x + b * y ∈ {c : ℤ | 0 < c ∧ (∃ d : ℤ, ∃ e : ℤ, c = a * d + b * e)} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := a * x + b * y))).mpr ⟨by parley_set_side, x, y, by parley_set_side⟩)
      exact hI
    -- 8.2. instantiate s := a·x + b·y in line 4, from 8.1
    exact (s4b (a * x + b * y) s8_1)
  -- 9. algebra
  have s9 : a = a * 1 + b * 0 := by parley_ring
  -- 10. thm:least-combination-divides c := a, u := 1, v := 0, from 6, 7, 8, 9
  have s10 : d ∣ a := by exact (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) hH2 (c := a) (d := d) s6 (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 (by parley_set_side))
  -- 11. thm:least-combination-divides c := b, u := 0, v := 1, from 1, 6, 7, 8
  have s11 : d ∣ b := by exact (Parley.Stdlib.Divisibility.LeastCombinationDivides.least_combination_divides (a := a) (b := b) hH2 (c := b) (d := d) s6 (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s1 s7 (by parley_set_side))
  -- 12. mun:gcd-integer
  have s12a : 0 ≤ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_1 (a := a) (b := b))
  have s12b : (Int.gcd a b : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := b))
  have s12c : (Int.gcd a b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b))
  -- 13. inequalities, from H2
  have s13 : b ≠ 0 := hH2.ne'
  -- 14. contradiction
  have s14 : ¬ (a = 0 ∧ b = 0) := by
    intro hS
    -- 14.1. restate 13
    have s14_1 : b ≠ 0 := by exact s13
    exact s14_1 hS.2
  -- 15. mun:gcd-natural, from 14
  have s15 : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_natural (a := a) (b := b) s14)
  -- 16. thm:divides-gcd, from 10, 11
  have s16 : d ∣ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := a) (b := b) s10 s11)
  -- 17. mun:divides-le e := d, m := gcd(a, b), from 6, 15, 16
  have s17 : d ≤ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) s6 (m := (Int.gcd a b : ℤ)) s15 s16)
  -- 18. mun:divides-combination e := gcd(a, b), x := x₀, y := y₀, from 12
  have s18 : (Int.gcd a b : ℤ) ∣ a * x₀ + b * y₀ := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s12b s12c)
  -- 19. substitute d = a·x₀ + b·y₀ (line 7) into line 18
  have s19 : (Int.gcd a b : ℤ) ∣ d := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd a b : ℤ) ∣ t)) s7.symm s18; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 20. mun:divides-le e := gcd(a, b), m := d, from 6, 15, 19
  have s20 : (Int.gcd a b : ℤ) ≤ d := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) s15 (m := d) s6 s19)
  -- 21. antisymmetry, from 17, 20
  have s21 : d = (Int.gcd a b : ℤ) := le_antisymm s17 s20
  -- 22. transitivity, from 7, 21
  have s22 : a * x₀ + b * y₀ = (Int.gcd a b : ℤ) := by exact Eq.trans s7.symm s21
  -- 23. exhibit, from 22
  exact ⟨x₀, y₀, s22⟩

end Parley.Stdlib.Divisibility.Bezout
