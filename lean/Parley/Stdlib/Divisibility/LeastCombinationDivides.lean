module

public import NormTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.LeastCombinationDivides

theorem least_combination_divides (a : ℤ) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (d : ℤ) (hH4 : 0 < d) (u : ℤ) (v : ℤ) (x₀ : ℤ) (y₀ : ℤ) (hH9 : c = a * u + b * v) (hH10 : d = a * x₀ + b * y₀) (hH11 : ∀ x : ℤ, ∀ y : ℤ, 0 < a * x + b * y → d ≤ a * x + b * y) :
    d ∣ c := by
  -- 1. mun:mod-natural a := c, b := d
  have s1 : 0 ≤ c % d := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := c) (b := d) hH4)
  -- 2. mun:mod-less a := c, b := d
  have s2 : c % d < d := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := c) (b := d) hH4)
  -- 3. obtain q: mun:mod-remainder a := c, m := d, r := c mod d, from 1, 2
  obtain ⟨q, s3⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := c) (m := d) hH4 (r := c % d) s1 s2)).mp rfl
  -- 4. algebra, from H9, H10, 3
  have s4 : c % d = a * (u - q * x₀) + b * (v - q * y₀) := by linear_combination (norm := parley_norm) hH9 + (-q) * hH10 + s3
  -- 5. contradiction
  have s5 : c % d = 0 := by
    by_contra (hS : c % d ≠ 0)
    -- 5.1. mun:pos-int-nat m := c mod d
    have r57_2 : 0 < c % d := Or.elim (Ne.lt_or_gt hS) (fun h1 => by linarith only [s1, h1]) (fun h1 => by linarith only [s1, h1])
    have s5_1 : 0 < c % d := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c % d) r57_2)
    -- 5.2. substitute c mod d = a·(u − q·x₀) + b·(v − q·y₀) (line 4) into line 5.1
    have s5_2 : 0 < a * (u - q * x₀) + b * (v - q * y₀) := by (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) s4 s5_1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 5.3. instantiate x := u − q·x₀, y := v − q·y₀ in H11, from 5.2
    have s5_3 : d ≤ a * (u - q * x₀) + b * (v - q * y₀) := by exact (hH11 (u - q * x₀) (v - q * y₀) s5_2)
    -- 5.4. substitute c mod d = a·(u − q·x₀) + b·(v − q·y₀) (line 4) into line 5.3
    have s5_4 : d ≤ c % d := by (have h := Eq.subst (motive := (fun t : ℤ => d ≤ t)) s4.symm s5_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 5.5. inequalities, from 2
    have s5_5 : ¬ d ≤ c % d := by linarith only [s2]
    exact s5_5 s5_4
  -- 6. algebra, from 3, 5
  have s6 : c = d * q := by linear_combination (norm := parley_norm) (-1) * s3 + s5
  -- 7. def:divides n := c, from 6
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := d) (n := c))).mpr ⟨q, s6⟩

end Parley.Stdlib.Divisibility.LeastCombinationDivides
