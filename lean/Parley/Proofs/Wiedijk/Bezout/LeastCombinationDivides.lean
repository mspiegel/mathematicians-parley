module

public import NormTactics
public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/bezout.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides

set_option maxHeartbeats 400000 in
theorem least_combination_divides (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (d : ℤ) (hH4 : 0 < d) (u : ℤ) (v : ℤ) (x₀ : ℤ) (y₀ : ℤ) (hH9 : c = a * u + b * v) (hH10 : d = a * x₀ + b * y₀) (hH11 : ∀ x : ℤ, ∀ y : ℤ, 0 < a * x + b * y → d ≤ a * x + b * y) :
    d ∣ c := by
  -- 1. obtain q, r: thm:division-algorithm n := c
  obtain ⟨q, r, ⟨⟨s1a, s1b⟩, s1c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_division_algorithm (n := c) (by parley_side) (d := d) (by parley_side))
  -- 2. algebra, from H9, H10, 1
  have s2 : r = a * (u - q * x₀) + b * (v - q * y₀) := by linear_combination (norm := parley_norm) hH9 + (-q) * hH10 + (-1) * s1a
  -- 3. contradiction
  have s3 : r = 0 := by
    by_contra (hS : r ≠ 0)
    -- 3.1. mun:pos-int-nat m := r
    have r39_1 : 0 < r := by parley_order
    have s3_1 : 0 < r := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := r) r39_1)
    -- 3.2. substitute r = a·(u − q·x₀) + b·(v − q·y₀) (line 2) into line 3.1
    have s3_2 : 0 < a * (u - q * x₀) + b * (v - q * y₀) := by (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) s2 s3_1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 3.3. instantiate x := u − q·x₀, y := v − q·y₀ in H11, from 3.2
    have s3_3 : d ≤ a * (u - q * x₀) + b * (v - q * y₀) := by exact (hH11 (u - q * x₀) (v - q * y₀) (by parley_side))
    -- 3.4. substitute r = a·(u − q·x₀) + b·(v − q·y₀) (line 2) into line 3.3
    have s3_4 : d ≤ r := by (have h := Eq.subst (motive := (fun t : ℤ => d ≤ t)) s2.symm s3_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 3.5. inequalities, from 1
    have s3_5 : ¬ d ≤ r := by parley_side
    exact s3_5 s3_4
  -- 4. substitute r = 0 (line 3) into line 1
  have s4 : c = q * d := by (have h := Eq.subst (motive := (fun t : ℤ => c = q * d + t)) s3 s1a; push_cast [add_zero] at h ⊢; all_goals exact_mod_cast h)
  -- 5. algebra, from 4
  have s5 : c = d * q := by linear_combination (norm := parley_norm) s4
  -- 6. def:divides n := c, from 5
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := d) (n := c))).mpr ⟨q, s5⟩

end Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides
