module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/cubic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Cubic.Cubic

set_option maxHeartbeats 1000000 in
theorem cubic (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (x : ℂ) (hH6 : a ≠ 0) (M : ℂ) (hH8 : M = b ^ 2 - 3 * a * c) (N : ℂ) (hH10 : N = 2 * b ^ 3 - 9 * a * b * c + 27 * a ^ 2 * d) (G : ℂ) (hH12 : G ^ 2 = N ^ 2 - 4 * M ^ 3) (T : ℂ) (hH14 : T ^ 3 = (N + G) / 2) (hH15 : T ≠ 0) :
    (a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ (∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a)))) := by
  -- 1. mun:i-complex
  -- 2. def:i
  have s2 : Complex.I * Complex.I = -1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Numbers.def_i | (have h := Parley.Items.Stdlib.Numbers.def_i; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.def_i; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Numbers.def_i | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_i).symm | (have h := Parley.Items.Stdlib.Numbers.def_i; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.def_i; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.def_i; parley_int_power h) | (have h := Parley.Items.Stdlib.Numbers.def_i; parley_set_side)
  -- 3. real arithmetic
  have s3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := by parley_real
  -- 4. algebra, from 1, 2, 3
  have s4 : (Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) ^ 2 = -3 := by
    have s3_w : (Real.sqrt (3 : ℝ) : ℂ) ^ 2 = 3 := by have h := congrArg (fun x : ℝ => (x : ℂ)) s3; push_cast at h; linear_combination (norm := parley_norm) h
    linear_combination (norm := parley_norm) ((Real.sqrt (3 : ℝ) : ℂ) ^ 2) * s2 + (-1) * s3_w
  set ω₁ : ℂ := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 with hD1
  have hD1_kind : True := by parley_set_side
  set ω₂ : ℂ := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 with hD2
  have hD2_kind : True := by parley_set_side
  -- 5. algebra, from D1, D2, 1, 4
  have s5 : ω₁ * ω₂ = 1 := by
    try simp only [hD1, hD2] at *
    try push_cast at *
    linear_combination (norm := parley_norm) ((-1) / ((4))) * s4
  -- 6. contradiction
  have s6 : ω₁ ≠ 0 := by
    by_contra hc_hS1
    have hS1 : ω₁ = 0 := by parley_suppose hc_hS1
    -- 6.1. algebra, from S1, 5
    have s6_1 : (1 : ℂ) = 0 := by linear_combination (norm := parley_norm) (ω₂) * hS1 + (-1) * s5
    exact absurd s6_1 (by norm_num)
    all_goals parley_set_side
  -- 7. contradiction
  have s7 : ω₂ ≠ 0 := by
    by_contra hc_hS2
    have hS2 : ω₂ = 0 := by parley_suppose hc_hS2
    -- 7.1. algebra, from S2, 5
    have s7_1 : (1 : ℂ) = 0 := by linear_combination (norm := parley_norm) (ω₁) * hS2 + (-1) * s5
    exact absurd s7_1 (by norm_num)
    all_goals parley_set_side
  -- 8. algebra, from H12, H14, H15
  have s8 : T ^ 3 + M ^ 3 / T ^ 3 = N := by linear_combination (norm := parley_field) (((1 / 4 : ℂ)) / ((T ^ 3))) * hH12 + ((2 * T ^ 3 + G - N) / ((T ^ 3) * (2))) * hH14
  set y : ℂ := 3 * a * x + b with hD3
  have hD3_kind : True := by parley_set_side
  set u : ℂ := y + T + M / T with hD4
  have hD4_kind : True := by parley_set_side
  set v : ℂ := y + ω₁ * T + M / (ω₁ * T) with hD5
  have hD5_kind : True := by parley_set_side
  set w : ℂ := y + ω₂ * T + M / (ω₂ * T) with hD6
  have hD6_kind : True := by parley_set_side
  -- 9. algebra, from D3, H6, H8, H10
  have s9 : a * x ^ 3 + b * x ^ 2 + c * x + d = (y ^ 3 - 3 * M * y + N) / (27 * a ^ 2) := by
    try simp only [hD3] at *
    try push_cast at *
    linear_combination (norm := parley_field) ((9 * a * x + 3 * b) / ((27 * a ^ 2))) * hH8 + ((-1) / ((27 * a ^ 2))) * hH10
  -- 10. algebra, from D1, D2, D5, D6, H15, 1, 4, 6, 7
  have s10 : v * w = y ^ 2 - (T + M / T) * y + T ^ 2 - M + M ^ 2 / T ^ 2 := by
    try simp only [hD1, hD2, hD5, hD6] at *
    try push_cast at *
    linear_combination (norm := parley_field) (((Real.sqrt (3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 * T ^ 4 - T ^ 4 - 4 * M * T * y + 4 * M * T ^ 2 + 4 * M ^ 2) / ((-4 * (Real.sqrt (3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 * T ^ 2 + 4 * T ^ 2))) * s4
  -- 11. calculation
  have s11 : y ^ 3 - 3 * M * y + N = u * (v * w) := by
    calc y ^ 3 - 3 * M * y + N = u * (y ^ 2 - (T + M / T) * y + T ^ 2 - M + M ^ 2 / T ^ 2) := by
          try simp only [hD4] at *
          try push_cast at *
          linear_combination (norm := parley_field) (-1) * s8
      _ = u * (v * w) := by parley_subst s10
  -- 12. both directions
  have s12 : a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ (∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a))) := by
    constructor
    · skip
      intro hA1
      -- 12.1. calculation
      have s12_1 : u * (v * w) = 0 := by
        calc u * (v * w) = y ^ 3 - 3 * M * y + N := by parley_set_side
          _ = 0 := by linear_combination (norm := parley_field) (27 * a ^ 2) * hA1 + (-27 * a ^ 2) * s9
      -- 12.2. mun:zero-product x := u, y := v·w, from 12.1
      have s12_2 : u = 0 ∨ v * w = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v * w))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v * w))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v * w))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v * w))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v * w))).mp (by parley_set_side); parley_set_side)
      -- 12.3. cases, from 12.2
      have s12_3 : ∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a)) := by
        rcases s12_2 with hC1 | hC2
        · skip
          -- 12.3.1. algebra, from C1, D3, D4, H6, H15
          have s12_3_1 : x = -((b + T + M / T) / (3 * a)) := by
            try simp only [hD3, hD4] at *
            try push_cast at *
            linear_combination (norm := parley_field) ((T) / ((3 * T * a))) * hC1
          -- 12.3.2. mun:triple-members
          have s12_3_2 : (1 : ℂ) ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ) := by first | exact (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | exact ((Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); parley_set_side)
          -- 12.3.3. exhibit, from 12.3.1, 12.3.2
          have s12_3_3 : ∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a)) := ⟨(1 : ℂ), by parley_set_side, by parley_set_side⟩
          all_goals parley_set_side
        · skip
          -- 12.3.4. mun:zero-product x := v, y := w, from C2
          have s12_3_4 : v = 0 ∨ w = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := v) (y := w))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := v) (y := w))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := v) (y := w))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := v) (y := w))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := v) (y := w))).mp (by parley_set_side); parley_set_side)
          -- 12.3.5. cases, from 12.3.4
          have s12_3_5 : ∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a)) := by
            rcases s12_3_4 with hC3 | hC4
            · skip
              -- 12.3.5.1. algebra, from C3, D1, D3, D5, H6, H15, 1, 6
              have s12_3_5_1 : x = -((b + (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T + M / ((-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T)) / (3 * a)) := by
                try simp only [hD1, hD3, hD5] at *
                try push_cast at *
                linear_combination (norm := parley_field) ((4 * (Real.sqrt (3 : ℝ) : ℂ) * Complex.I * T - 4 * T) / ((6 * (Real.sqrt (3 : ℝ) : ℂ) * Complex.I * T * a - 6 * T * a) * (2))) * hC3
              -- 12.3.5.2. mun:triple-members
              have s12_3_5_2 : (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ) := by first | exact (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | exact ((Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); parley_set_side)
              -- 12.3.5.3. exhibit, from 12.3.5.1, 12.3.5.2
              have s12_3_5_3 : ∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a)) := ⟨(-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, by parley_set_side, by parley_set_side⟩
              all_goals parley_set_side
            · skip
              -- 12.3.5.4. algebra, from C4, D2, D3, D6, H6, H15, 1, 7
              have s12_3_5_4 : x = -((b + (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T + M / ((-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T)) / (3 * a)) := by
                try simp only [hD2, hD3, hD6] at *
                try push_cast at *
                linear_combination (norm := parley_field) ((-4 * (Real.sqrt (3 : ℝ) : ℂ) * Complex.I * T - 4 * T) / ((-6 * (Real.sqrt (3 : ℝ) : ℂ) * Complex.I * T * a - 6 * T * a) * (2))) * hC4
              -- 12.3.5.5. mun:triple-members
              have s12_3_5_5 : (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ) := by first | exact (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | exact ((Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (v := (1 : ℂ)) (w := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2)); parley_set_side)
              -- 12.3.5.6. exhibit, from 12.3.5.4, 12.3.5.5
              have s12_3_5_6 : ∃ r ∈ ({(1 : ℂ), (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2} : Set ℂ), x = -((b + r * T + M / (r * T)) / (3 * a)) := ⟨(-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2, by parley_set_side, by parley_set_side⟩
              all_goals parley_set_side
          all_goals parley_set_side
      all_goals parley_set_side
    · skip
      intro hA2
      -- 12.4. obtain r from A2
      obtain ⟨r, s12_4a, s12_4b⟩ := hA2
      -- 12.5. def:triple x := r, from 12.4
      have s12_5 : (r = 1 ∨ r = (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) ∨ r = (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 := by first | exact ((Parley.Items.Stdlib.Sets.def_triple (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (x := r))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_triple (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (x := r))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_triple (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (x := r))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_triple (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (x := r))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_triple (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (x := r))).mp (by parley_set_side); parley_rat_of_real h) | (have h := ((Parley.Items.Stdlib.Sets.def_triple (u := (1 : ℂ)) (v := (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (w := (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2) (x := r))).mp (by parley_set_side); parley_set_side)
      -- 12.6. cases, from 12.5
      have s12_6 : u * (v * w) = 0 := by
        rcases s12_5 with (hC6 | hC7) | hC8
        · skip
          -- 12.6.1. substitute r = 1 (C6) into line 12.4
          have s12_6_1 : x = -((b + 1 * T + M / (1 * T)) / (3 * a)) := by parley_subst_at hC6 s12_4b
          -- 12.6.2. algebra, from D3, D4, H6, H15, 12.6.1
          have s12_6_2 : u = 0 := by
            try simp only [hD3, hD4] at *
            try push_cast at *
            linear_combination (norm := parley_field) (3 * a) * s12_6_1
          -- 12.6.3. algebra, from 12.6.2
          have s12_6_3 : u * (v * w) = 0 := by linear_combination (norm := parley_norm) (v * w) * s12_6_2
          all_goals parley_set_side
        · skip
          -- 12.6.4. substitute r = (−1 + i·√3)/2 (C7) into line 12.4
          have s12_6_4 : x = -((b + (-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T + M / ((-1 + Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T)) / (3 * a)) := by parley_subst_at hC7 s12_4b
          -- 12.6.5. algebra, from D1, D3, D5, H6, H15, 1, 6, 12.6.4
          have s12_6_5 : v = 0 := by
            try simp only [hD1, hD3, hD5] at *
            try push_cast at *
            linear_combination (norm := parley_field) ((6 * a) / ((2))) * s12_6_4
          -- 12.6.6. algebra, from 12.6.5
          have s12_6_6 : u * (v * w) = 0 := by linear_combination (norm := parley_norm) (u * w) * s12_6_5
          all_goals parley_set_side
        · skip
          -- 12.6.7. substitute r = (−1 − i·√3)/2 (C8) into line 12.4
          have s12_6_7 : x = -((b + (-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T + M / ((-1 - Complex.I * (Real.sqrt (3 : ℝ) : ℂ)) / 2 * T)) / (3 * a)) := by parley_subst_at hC8 s12_4b
          -- 12.6.8. algebra, from D2, D3, D6, H6, H15, 1, 7, 12.6.7
          have s12_6_8 : w = 0 := by
            try simp only [hD2, hD3, hD6] at *
            try push_cast at *
            linear_combination (norm := parley_field) ((6 * a) / ((2))) * s12_6_7
          -- 12.6.9. algebra, from 12.6.8
          have s12_6_9 : u * (v * w) = 0 := by linear_combination (norm := parley_norm) (u * v) * s12_6_8
          all_goals parley_set_side
      -- 12.7. calculation
      have s12_7 : y ^ 3 - 3 * M * y + N = 0 := by
        calc y ^ 3 - 3 * M * y + N = u * (v * w) := by parley_set_side
          _ = 0 := by parley_set_side
      -- 12.8. calculation
      have s12_8 : a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
        calc a * x ^ 3 + b * x ^ 2 + c * x + d = (y ^ 3 - 3 * M * y + N) / (27 * a ^ 2) := by parley_set_side
          _ = 0 / (27 * a ^ 2) := by parley_subst s12_7
          _ = 0 := by parley_ring
      all_goals parley_set_side
  all_goals exact s12

end Parley.Proofs.Wiedijk.Cubic.Cubic
