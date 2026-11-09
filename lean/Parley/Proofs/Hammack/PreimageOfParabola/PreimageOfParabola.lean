module

public import AlgebraTactics
public import OrderTactics
public import RealTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn
public import Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut

/-! Written from proofs/hammack/preimage-of-parabola.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfParabola.PreimageOfParabola

set_option maxHeartbeats 1000000 in
theorem preimage_of_parabola (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x ^ 2 + 3) :
    (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) = (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ) := by
  -- 1. proof
  have s1 : ∀ u ∈ (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ), u ∈ (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ) := by
    intro u hK1
    -- 1.1. def:preimage Z := [12, 19], from K1
    have s1_1 : f u ∈ (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) := by first | exact (((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mp hK1).2 | exact ((((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mp hK1).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mp hK1).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mp hK1).2 | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mp hK1).2; parley_rat_of_real h) | (have h := (((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mp hK1).2; parley_set_side)
    -- 1.2. def:interval a := 12, b := 19, x := f(u), from 1.1
    have s1_2a : 12 ≤ f u := (((Parley.Items.Stdlib.Calculus.def_interval (x := f u) (a := (12 : ℝ)) (b := (19 : ℝ)))).mp s1_1).1.2
    have s1_2b : f u ≤ 19 := (((Parley.Items.Stdlib.Calculus.def_interval (x := f u) (a := (12 : ℝ)) (b := (19 : ℝ)))).mp s1_1).2
    -- 1.3. instantiate x := u in H2, from 1.1
    have s1_3 : f u = u ^ 2 + 3 := by exact (hH2 u)
    -- 1.4. calculation
    have s1_4 : 12 ≤ u ^ 2 + 3 := by
      calc (12 : ℝ) ≤ f u := by parley_set_side
        _ = u ^ 2 + 3 := by parley_set_side
    -- 1.5. calculation
    have s1_5 : u ^ 2 + 3 ≤ 19 := by
      calc u ^ 2 + 3 = f u := by parley_set_side
        _ ≤ 19 := by parley_set_side
    -- 1.6. mun:nonneg-or-neg x := u, from 1.1
    have s1_6 : u ≥ 0 ∨ u < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := u))
    -- 1.7. cases, from 1.6
    rcases s1_6 with hC1 | hC2
    · skip
      -- 1.7.1. thm:square-window-out t := u, from C1, 1.1, 1.4, 1.5
      have s1_7_1a : 3 ≤ u := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut.square_window_out (t := u) (by parley_set_side) (by parley_set_side) (by parley_set_side)).1
      have s1_7_1b : u ≤ 4 := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut.square_window_out (t := u) (by parley_set_side) (by parley_set_side) (by parley_set_side)).2
      -- 1.7.2. def:interval a := 3, b := 4, x := u, from 1.1, 1.7.1
      have s1_7_2 : u ∈ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := u) (a := (3 : ℝ)) (b := (4 : ℝ)))).mpr (by parley_set_side)
      -- 1.7.3. mun:in-union-right Y := [−4, −3], Z := [3, 4], from 1.7.2
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ)) (Z := (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ)) (u := u) s1_7_2)
    · skip
      -- 1.7.4. inequalities
      have s1_7_4 : -u ≥ 0 := by parley_order
      -- 1.7.5. algebra, from 1.1
      have s1_7_5 : (-u) ^ 2 + 3 = u ^ 2 + 3 := by parley_ring
      -- 1.7.6. calculation
      have s1_7_6 : 12 ≤ (-u) ^ 2 + 3 := by
        calc (12 : ℝ) ≤ u ^ 2 + 3 := by parley_set_side
          _ = (-u) ^ 2 + 3 := by parley_set_side
      -- 1.7.7. calculation
      have s1_7_7 : (-u) ^ 2 + 3 ≤ 19 := by
        calc (-u) ^ 2 + 3 = u ^ 2 + 3 := by parley_set_side
          _ ≤ 19 := by parley_set_side
      -- 1.7.8. thm:square-window-out t := −u, from 1.1, 1.7.4, 1.7.6, 1.7.7
      have s1_7_8a : 3 ≤ -u := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut.square_window_out (t := -u) (by parley_set_side) (by parley_set_side) (by parley_set_side)).1
      have s1_7_8b : -u ≤ 4 := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut.square_window_out (t := -u) (by parley_set_side) (by parley_set_side) (by parley_set_side)).2
      -- 1.7.9. inequalities
      have s1_7_9 : -4 ≤ u := by parley_order
      -- 1.7.10. inequalities
      have s1_7_10 : u ≤ -3 := by parley_order
      -- 1.7.11. def:interval a := −4, b := −3, x := u, from 1.1, 1.7.9, 1.7.10
      have s1_7_11 : u ∈ (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := u) (a := (-4 : ℝ)) (b := (-3 : ℝ)))).mpr (by parley_set_side)
      -- 1.7.12. mun:in-union-left Y := [−4, −3], Z := [3, 4], from 1.7.11
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ)) (Z := (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ)) (u := u) s1_7_11)
  -- 2. def:subset, from 1
  have s2 : (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) ⊆ (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Sets.def_subset (X := (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (Y := (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ)))).mpr s1
  -- 3. proof
  have s3 : ∀ u ∈ (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ), u ∈ (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) := by
    intro u hK2
    -- 3.1. def:union, from K2
    have s3_1 : u ∈ (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∨ u ∈ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Sets.def_union (Y := (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ)) (Z := (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ)) (u := u))).mp hK2
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC3 | hC4
    · skip
      -- 3.2.1. def:interval a := −4, b := −3, x := u, from C3
      have s3_2_1a : -4 ≤ u := (((Parley.Items.Stdlib.Calculus.def_interval (x := u) (a := (-4 : ℝ)) (b := (-3 : ℝ)))).mp hC3).1.2
      have s3_2_1b : u ≤ -3 := (((Parley.Items.Stdlib.Calculus.def_interval (x := u) (a := (-4 : ℝ)) (b := (-3 : ℝ)))).mp hC3).2
      -- 3.2.2. inequalities
      have s3_2_2 : 3 ≤ -u := by parley_order
      -- 3.2.3. inequalities
      have s3_2_3 : -u ≤ 4 := by parley_order
      -- 3.2.4. thm:square-window-in t := −u, from 3.2.1, 3.2.2, 3.2.3
      have s3_2_4a : 12 ≤ (-u) ^ 2 + 3 := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn.square_window_in (t := -u) s3_2_2 s3_2_3).1
      have s3_2_4b : (-u) ^ 2 + 3 ≤ 19 := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn.square_window_in (t := -u) s3_2_2 s3_2_3).2
      -- 3.2.5. algebra, from 3.2.1
      have s3_2_5 : (-u) ^ 2 + 3 = u ^ 2 + 3 := by parley_ring
      -- 3.2.6. instantiate x := u in H2, from 3.2.1
      have s3_2_6 : f u = u ^ 2 + 3 := by exact (hH2 u)
      -- 3.2.7. calculation
      have s3_2_7 : 12 ≤ f u := by
        calc (12 : ℝ) ≤ (-u) ^ 2 + 3 := by parley_set_side
          _ = u ^ 2 + 3 := by parley_set_side
          _ = f u := by parley_set_side
      -- 3.2.8. calculation
      have s3_2_8 : f u ≤ 19 := by
        calc f u = u ^ 2 + 3 := by parley_set_side
          _ = (-u) ^ 2 + 3 := by parley_set_side
          _ ≤ 19 := by parley_set_side
      -- 3.2.9. membership, from 3.2.1, 3.2.6
      -- 3.2.10. def:interval a := 12, b := 19, x := f(u), from 3.2.7, 3.2.8, 3.2.9
      have s3_2_10 : f u ∈ (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := f u) (a := (12 : ℝ)) (b := (19 : ℝ)))).mpr (by parley_set_side)
      -- 3.2.11. def:preimage Z := [12, 19], from 3.2.1, 3.2.10
      exact ((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mpr (by parley_set_side)
    · skip
      -- 3.2.12. def:interval a := 3, b := 4, x := u, from C4
      have s3_2_12a : 3 ≤ u := (((Parley.Items.Stdlib.Calculus.def_interval (x := u) (a := (3 : ℝ)) (b := (4 : ℝ)))).mp hC4).1.2
      have s3_2_12b : u ≤ 4 := (((Parley.Items.Stdlib.Calculus.def_interval (x := u) (a := (3 : ℝ)) (b := (4 : ℝ)))).mp hC4).2
      -- 3.2.13. thm:square-window-in t := u, from 3.2.12
      have s3_2_13a : 12 ≤ u ^ 2 + 3 := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn.square_window_in (t := u) s3_2_12a s3_2_12b).1
      have s3_2_13b : u ^ 2 + 3 ≤ 19 := by exact (Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn.square_window_in (t := u) s3_2_12a s3_2_12b).2
      -- 3.2.14. instantiate x := u in H2, from 3.2.12
      have s3_2_14 : f u = u ^ 2 + 3 := by exact (hH2 u)
      -- 3.2.15. calculation
      have s3_2_15 : 12 ≤ f u := by
        calc (12 : ℝ) ≤ u ^ 2 + 3 := by parley_set_side
          _ = f u := by parley_set_side
      -- 3.2.16. calculation
      have s3_2_16 : f u ≤ 19 := by
        calc f u = u ^ 2 + 3 := by parley_set_side
          _ ≤ 19 := by parley_set_side
      -- 3.2.17. membership, from 3.2.12, 3.2.14
      -- 3.2.18. def:interval a := 12, b := 19, x := f(u), from 3.2.15, 3.2.16, 3.2.17
      have s3_2_18 : f u ∈ (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := f u) (a := (12 : ℝ)) (b := (19 : ℝ)))).mpr (by parley_set_side)
      -- 3.2.19. def:preimage Z := [12, 19], from 3.2.12, 3.2.18
      exact ((Parley.Items.Stdlib.Functions.def_preimage (X := (Set.univ : Set ℝ)) (Z := (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (f := f) (u := u) (W := Set.univ) (by parley_whole_side))).mpr (by parley_set_side)
  -- 4. def:subset, from 3
  have s4 : (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Sets.def_subset (X := (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (Set.univ : Set ℝ) ∩ f ⁻¹' (Set.Icc (12 : ℝ) (19 : ℝ) : Set ℝ)) (Y := (Set.Icc (-4 : ℝ) (-3 : ℝ) : Set ℝ) ∪ (Set.Icc (3 : ℝ) (4 : ℝ) : Set ℝ)) s2 s4)

end Parley.Proofs.Hammack.PreimageOfParabola.PreimageOfParabola
