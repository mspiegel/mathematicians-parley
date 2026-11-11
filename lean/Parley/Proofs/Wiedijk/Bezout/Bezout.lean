module

public import AlgebraTactics
public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
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
public import Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides

/-! Written from proofs/wiedijk/bezout.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Bezout.Bezout

theorem bezout (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) :
    (∃ x : ℤ, ∃ y : ℤ, a * x + b * y = (Int.gcd a b : ℤ)) := by
  set S : Set ℤ := {t : ℤ | 0 < t ∧ (∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)} with hD1
  -- 1. algebra
  have s1 : a = a * 1 + b * 0 := by parley_ring
  -- 2. def:set-builder u := a, from D1, 1
  have s2 : a ∈ S := by
    have hI : a ∈ {c : ℤ | 0 < c ∧ (∃ d : ℤ, ∃ e : ℤ, c = a * d + b * e)} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : ℤ => ∃ m : ℤ, ∃ n : ℤ, t = a * m + b * n)) (X := {n : ℤ | 0 < n}) (u := a))).mpr ⟨by parley_set_side, (1 : ℤ), (0 : ℤ), s1⟩)
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
  have s10 : d ∣ a := by exact (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) hH1 (b := b) hH2 (c := a) hH1 (d := d) s6 (u := (1 : ℤ)) (v := (0 : ℤ)) (x₀ := x₀) (y₀ := y₀) s9 s7 (by parley_set_side))
  -- 11. algebra
  have s11 : b = a * 0 + b * 1 := by parley_ring
  -- 12. thm:least-combination-divides c := b, u := 0, v := 1, from 6, 7, 8, 11
  have s12 : d ∣ b := by exact (Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides.least_combination_divides (a := a) hH1 (b := b) hH2 (c := b) hH2 (d := d) s6 (u := (0 : ℤ)) (v := (1 : ℤ)) (x₀ := x₀) (y₀ := y₀) s11 s7 (by parley_set_side))
  -- 13. def:gcd
  have s13a : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) hH1 (b := b) hH2)
  have s13b : (Int.gcd a b : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) hH1 (b := b) hH2)
  have s13c : (Int.gcd a b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) hH1 (b := b) hH2)
  have s13d : ∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) hH1 (b := b) hH2)
  -- 14. instantiate e := d in line 13, from 6, 10, 12
  have s14 : d ≤ (Int.gcd a b : ℤ) := by exact (s13d d s6 (by parley_set_side))
  -- 15. mun:divides-combination e := gcd(a, b), x := x₀, y := y₀, from 13
  have s15 : (Int.gcd a b : ℤ) ∣ a * x₀ + b * y₀ := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd a b : ℤ)) (a := a) (b := b) (x := x₀) (y := y₀) s13b s13c)
  -- 16. substitute d = a·x₀ + b·y₀ (line 7) into line 15
  have s16 : (Int.gcd a b : ℤ) ∣ d := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd a b : ℤ) ∣ t)) s7.symm s15; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 17. mun:divides-le e := gcd(a, b), m := d, from 6, 13, 16
  have s17 : (Int.gcd a b : ℤ) ≤ d := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd a b : ℤ)) s13a (m := d) s6 s16)
  -- 18. antisymmetry, from 14, 17
  have s18 : d = (Int.gcd a b : ℤ) := by parley_set_side
  -- 19. calculation
  have s19 : a * x₀ + b * y₀ = (Int.gcd a b : ℤ) := by
    calc a * x₀ + b * y₀ = d := by parley_set_side
      _ = (Int.gcd a b : ℤ) := by exact s18
  -- 20. exhibit, from 19
  exact ⟨x₀, y₀, s19⟩

end Parley.Proofs.Wiedijk.Bezout.Bezout
