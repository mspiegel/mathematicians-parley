module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/mobius-inverse.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MobiusInverse.MobiusInverse

set_option maxHeartbeats 400000 in
theorem mobius_inverse (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) ∧ Set.InjOn f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) ∧ Set.SurjOn f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ))) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ), f x = (5 * x + 1) / (x - 2)) :
    (∀ y ∈ (Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ), (LeanBridges.Functions.inverse f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ))) y = (2 * y + 1) / (y - 5)) := by
  -- 1. def:one-to-one-onto, from H1
  have s1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) ∧ Set.InjOn f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) := by exact (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) (f := f) (by parley_set_side))).mp hH1).1
  -- 2. def:one-to-one-onto, from H1
  have s2 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) ∧ Set.SurjOn f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) := by exact (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) (f := f) (by parley_set_side))).mp hH1).2
  -- 3. def:onto, from 2
  have s3 : ∀ y ∈ (Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ), ∃ x ∈ (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ), y = f x := by exact (((Parley.Items.Stdlib.Functions.def_onto (X := (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) (f := f) (by parley_set_side))).mp s2).2
  -- 4. proof
  intro y hK1
  -- 4.1. mun:remove-member u := y, Y := ℝ, a := 5, from K1
  have s4_1 : y ≠ 5 := by
    have hI : y ≠ 5 := by parley_instance ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (5 : ℝ)) (u := y))).mp hK1).2)
    exact hI
  -- 4.2. obtain x from line 3
  obtain ⟨x, s4_2a, s4_2b⟩ := (s3 y (by parley_set_side))
  -- 4.3. mun:remove-member u := x, Y := ℝ, a := 2, from 4.2
  have s4_3 : x ≠ 2 := by
    have hI : x ≠ 2 := by parley_instance ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := x))).mp s4_2a).2)
    exact hI
  -- 4.4. calculation
  have s4_4 : y = (5 * x + 1) / (x - 2) := by
    calc y = f x := by parley_set_side
      _ = (5 * x + 1) / (x - 2) := by exact (hH2 x (by parley_set_side))
  -- 4.5. mun:inverse-value g := f, y := x, from 1, 4.2
  have s4_5 : (LeanBridges.Functions.inverse f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ))) (f x) = x := by exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ) \ ({(5 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (g := f) (y := x) s1 s4_2a)
  -- 4.6. substitute y = f(x) (line 4.2) into line 4.5
  have s4_6 : (LeanBridges.Functions.inverse f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ))) y = x := by (have h := Eq.subst (motive := (fun t : ℝ => (LeanBridges.Functions.inverse f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ))) t = x)) s4_2b.symm s4_5; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4.7. calculation
  have r46_1 : x - 2 ≠ 0 := by parley_set_side
  have r46_2 : y - 5 ≠ 0 := by parley_set_side
  calc (LeanBridges.Functions.inverse f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ))) y = x := by exact s4_6
    _ = (2 * y + 1) / (y - 5) := by linear_combination (norm := parley_field) ((x - 2) / ((y - 5))) * s4_4

end Parley.Proofs.Hammack.MobiusInverse.MobiusInverse
