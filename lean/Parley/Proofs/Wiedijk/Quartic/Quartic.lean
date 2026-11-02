module

public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from proofs/wiedijk/quartic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Quartic.Quartic

theorem quartic (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (x : ℂ) (P : ℂ) (hH7 : P = b - 3 / 8 * a ^ 2) (Q : ℂ) (hH9 : Q = c - a * b / 2 + a ^ 3 / 8) (R : ℂ) (hH11 : R = d - c * a / 4 + (a ^ 2 * b / 16 - 3 / 256 * a ^ 4)) (U : ℂ) (hH13 : U = P ^ 2 + 12 * R) (V : ℂ) (hH15 : V = -(2 * P ^ 3) - 27 * Q ^ 2 + 72 * (P * R)) (W : ℂ) (hH17 : W ^ 2 = V ^ 2 - 4 * U ^ 3) (T : ℂ) (hH19 : T ^ 3 = (V + W) / 2) (hH20 : T ≠ 0) (M : ℂ) (hH22 : M = -((2 * P + T + U / T) / 3)) (hH23 : M ≠ 0) (S : ℂ) (hH25 : 4 * S ^ 2 = M) (I : ℂ) (hH27 : I ^ 2 = -(S ^ 2) - P / 2 + Q / 4 / S) (J : ℂ) (hH29 : J ^ 2 = -(S ^ 2) - P / 2 - Q / 4 / S) :
    (x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ (x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) ∨ x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) := by
  -- 1. contradiction
  have s1 : S ≠ 0 := by
    by_contra hc_hS1
    have hS1 : S = 0 := by parley_suppose hc_hS1
    -- 1.1. algebra, from H25, S1
    have s1_1 : M = 0 := by linear_combination (norm := parley_norm) (-1) * hH25 + (4 * S) * hS1
    all_goals parley_side
  -- 2. algebra, from H17, H19, H20
  have s2 : T ^ 3 + U ^ 3 / T ^ 3 = V := by linear_combination (norm := parley_field) (((1 / 4 : ℂ)) / ((T ^ 3))) * hH17 + ((2 * T ^ 3 - V + W) / ((T ^ 3) * (2))) * hH19
  -- 3. algebra, from H20, 2
  have s3 : (T + U / T) ^ 3 - 3 * U * (T + U / T) - V = 0 := by linear_combination (norm := parley_field) s2
  -- 4. algebra, from H20, H22
  have s4 : T + U / T = -(3 * M) - 2 * P := by linear_combination (norm := parley_field) ((9) / ((3))) * hH22
  -- 5. calculation
  have s5 : 27 * (M * (P + M) ^ 2 - Q ^ 2 - 4 * R * M) = 0 := by
    calc 27 * (M * (P + M) ^ 2 - Q ^ 2 - 4 * R * M) = -((-(3 * M) - 2 * P) ^ 3) + 3 * U * (-(3 * M) - 2 * P) + V := by linear_combination (norm := parley_norm) (9 * M + 6 * P) * hH13 + (-1) * hH15
      _ = -((T + U / T) ^ 3) + 3 * U * (T + U / T) + V := by parley_subst s4
      _ = 0 := by linear_combination (norm := parley_field) (-1) * s3
  -- 6. algebra, from 5
  have s6 : M * (P + M) ^ 2 - Q ^ 2 - 4 * R * M = 0 := by linear_combination (norm := parley_norm) ((1 / 27 : ℂ)) * s5
  set y : ℂ := x + a / 4 with hD1
  set u : ℂ := (y + S - I) * (y + S + I) with hD2
  set v : ℂ := (y - S - J) * (y - S + J) with hD3
  -- 7. algebra, from D2, H27, 1
  have s7 : u = y ^ 2 + 2 * S * y + 2 * S ^ 2 + P / 2 - Q / 4 / S := by
    try simp only [hD2] at *
    try push_cast at *
    linear_combination (norm := parley_field) ((-8) / ((8))) * hH27
  -- 8. algebra, from D3, H29, 1
  have s8 : v = y ^ 2 - 2 * S * y + 2 * S ^ 2 + P / 2 + Q / 4 / S := by
    try simp only [hD3] at *
    try push_cast at *
    linear_combination (norm := parley_field) ((-8) / ((8))) * hH29
  -- 9. calculation
  have s9 : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = u * v := by
    calc x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = y ^ 4 + (b - 3 / 8 * a ^ 2) * y ^ 2 + (c - a * b / 2 + a ^ 3 / 8) * y + (d - c * a / 4 + (a ^ 2 * b / 16 - 3 / 256 * a ^ 4)) := by
          try simp only [hD1] at *
          try push_cast at *
          parley_ring
      _ = y ^ 4 + P * y ^ 2 + (c - a * b / 2 + a ^ 3 / 8) * y + (d - c * a / 4 + (a ^ 2 * b / 16 - 3 / 256 * a ^ 4)) := by parley_subst hH7
      _ = y ^ 4 + P * y ^ 2 + Q * y + (d - c * a / 4 + (a ^ 2 * b / 16 - 3 / 256 * a ^ 4)) := by parley_subst hH9
      _ = y ^ 4 + P * y ^ 2 + Q * y + R := by parley_subst hH11
      _ = (y ^ 2 + 2 * S * y + 2 * S ^ 2 + P / 2 - Q / 4 / S) * (y ^ 2 - 2 * S * y + 2 * S ^ 2 + P / 2 + Q / 4 / S) := by linear_combination (norm := parley_field) ((-64 * S ^ 4 - 16 * M * S ^ 2 - 32 * P * S ^ 2 - 8 * M * P - 4 * M ^ 2 - 4 * P ^ 2 + 16 * R) / ((64 * S ^ 2))) * hH25 + ((-4) / ((64 * S ^ 2))) * s6
      _ = (y ^ 2 + 2 * S * y + 2 * S ^ 2 + P / 2 - Q / 4 / S) * v := by parley_subst s8
      _ = u * v := by parley_subst s7
  -- 10. both directions
  have s10 : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ (x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) ∨ x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by
    constructor
    · skip
      intro hA1
      -- 10.1. calculation
      have s10_1 : u * v = 0 := by
        calc u * v = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d := by parley_side
          _ = 0 := by parley_side
      -- 10.2. mun:zero-product x := u, y := v, from 10.1
      have s10_2 : u = 0 ∨ v = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := u) (y := v))).mp (by parley_side)
      -- 10.3. cases, from 10.2
      have s10_3 : (x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) ∨ x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by
        rcases s10_2 with hC1 | hC4
        · skip
          -- 10.3.1. mun:zero-product x := y + S − I, y := y + S + I, from C1, D2
          have s10_3_1 : y + S - I = 0 ∨ y + S + I = 0 := by
            try simp only [hD2] at *
            try push_cast at *
            first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y + S - I) (y := y + S + I))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y + S - I) (y := y + S + I))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y + S - I) (y := y + S + I))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y + S - I) (y := y + S + I))).mp (by parley_side)
          -- 10.3.2. cases, from 10.3.1
          have s10_3_2 : x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I := by
            rcases s10_3_1 with hC2 | hC3
            · skip
              -- 10.3.2.1. algebra, from C2, D1
              have s10_3_2_1 : x = -(a / 4) - S + I := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC2
              -- 10.3.2.2. mun:or-left, from 10.3.2.1
              have s10_3_2_2 : x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side))
              all_goals parley_side
            · skip
              -- 10.3.2.3. algebra, from C3, D1
              have s10_3_2_3 : x = -(a / 4) - S - I := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC3
              -- 10.3.2.4. mun:or-right, from 10.3.2.3
              have s10_3_2_4 : x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I) (Q := x = -(a / 4) - S - I) (by parley_side))
              all_goals parley_side
          -- 10.3.3. mun:or-left, from 10.3.2
          have s10_3_3 : (x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) ∨ x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side))
          all_goals parley_side
        · skip
          -- 10.3.4. mun:zero-product x := y − S − J, y := y − S + J, from C4, D3
          have s10_3_4 : y - S - J = 0 ∨ y - S + J = 0 := by
            try simp only [hD3] at *
            try push_cast at *
            first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y - S - J) (y := y - S + J))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y - S - J) (y := y - S + J))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y - S - J) (y := y - S + J))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := y - S - J) (y := y - S + J))).mp (by parley_side)
          -- 10.3.5. cases, from 10.3.4
          have s10_3_5 : x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by
            rcases s10_3_4 with hC5 | hC6
            · skip
              -- 10.3.5.1. algebra, from C5, D1
              have s10_3_5_1 : x = -(a / 4) + S + J := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC5
              -- 10.3.5.2. mun:or-left, from 10.3.5.1
              have s10_3_5_2 : x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side))
              all_goals parley_side
            · skip
              -- 10.3.5.3. algebra, from C6, D1
              have s10_3_5_3 : x = -(a / 4) + S - J := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC6
              -- 10.3.5.4. mun:or-right, from 10.3.5.3
              have s10_3_5_4 : x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) + S + J) (Q := x = -(a / 4) + S - J) (by parley_side))
              all_goals parley_side
          -- 10.3.6. mun:or-right, from 10.3.5
          have s10_3_6 : (x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) ∨ x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) (Q := x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) (by parley_side))
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hA2
      -- 10.4. cases, from A2
      have s10_4 : u * v = 0 := by
        rcases (show (x = -(a / 4) - S + I ∨ x = -(a / 4) - S - I) ∨ (x = -(a / 4) + S + J ∨ x = -(a / 4) + S - J) by have := hA2; tauto) with hC7 | hC10
        · skip
          -- 10.4.1. cases, from C7
          have s10_4_1 : u * v = 0 := by
            rcases hC7 with hC8 | hC9
            · skip
              -- 10.4.1.1. algebra, from C8, D1
              have s10_4_1_1 : y + S - I = 0 := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC8
              -- 10.4.1.2. algebra, from D2, 10.4.1.1
              have s10_4_1_2 : u * v = 0 := by
                try simp only [hD2] at *
                try push_cast at *
                linear_combination (norm := parley_norm) (I * v + S * v + v * y) * s10_4_1_1
              all_goals parley_side
            · skip
              -- 10.4.1.3. algebra, from C9, D1
              have s10_4_1_3 : y + S + I = 0 := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC9
              -- 10.4.1.4. algebra, from D2, 10.4.1.3
              have s10_4_1_4 : u * v = 0 := by
                try simp only [hD2] at *
                try push_cast at *
                linear_combination (norm := parley_norm) (-I * v + S * v + v * y) * s10_4_1_3
              all_goals parley_side
          all_goals parley_side
        · skip
          -- 10.4.2. cases, from C10
          have s10_4_2 : u * v = 0 := by
            rcases hC10 with hC11 | hC12
            · skip
              -- 10.4.2.1. algebra, from C11, D1
              have s10_4_2_1 : y - S - J = 0 := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC11
              -- 10.4.2.2. algebra, from D3, 10.4.2.1
              have s10_4_2_2 : u * v = 0 := by
                try simp only [hD3] at *
                try push_cast at *
                linear_combination (norm := parley_norm) (J * u - S * u + u * y) * s10_4_2_1
              all_goals parley_side
            · skip
              -- 10.4.2.3. algebra, from C12, D1
              have s10_4_2_3 : y - S + J = 0 := by
                try simp only [hD1] at *
                try push_cast at *
                linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * hC12
              -- 10.4.2.4. algebra, from D3, 10.4.2.3
              have s10_4_2_4 : u * v = 0 := by
                try simp only [hD3] at *
                try push_cast at *
                linear_combination (norm := parley_norm) (-J * u - S * u + u * y) * s10_4_2_3
              all_goals parley_side
          all_goals parley_side
      -- 10.5. calculation
      have s10_5 : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
        calc x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = u * v := by parley_side
          _ = 0 := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Wiedijk.Quartic.Quartic
