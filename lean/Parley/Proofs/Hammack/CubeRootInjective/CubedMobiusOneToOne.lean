module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.CubeRootInjective.CubeInjective

/-! Written from proofs/hammack/cube-root-injective.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeRootInjective.CubedMobiusOneToOne

theorem cubed_mobius_one_to_one (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ))) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), f x = ((x + 1) / (x - 1)) ^ 3) :
    (Set.MapsTo f ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) ∧ Set.InjOn f ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ))) := by
  -- 1. proof
  have s1 : ∀ s ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), ∀ t ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), f s = f t → s = t := by
    intro s hK1
    intro t hK2
    intro hA1
    -- 1.1. mun:remove-member u := s, Y := ℝ, a := 1, from K1
    have s1_1 : s ≠ 1 := by
      have hI : s ≠ 1 := by parley_instance ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (u := s))).mp hK1).2)
      exact hI
    -- 1.2. mun:remove-member u := t, Y := ℝ, a := 1, from K2
    have s1_2 : t ≠ 1 := by
      have hI : t ≠ 1 := by parley_instance ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (u := t))).mp hK2).2)
      exact hI
    -- 1.3. algebra, from 1.1
    have s1_3 : s - 1 ≠ 0 := by intro h; exact s1_1 (by linear_combination (norm := parley_norm) h)
    -- 1.4. algebra, from 1.2
    have s1_4 : t - 1 ≠ 0 := by intro h; exact s1_2 (by linear_combination (norm := parley_norm) h)
    -- 1.5. calculation
    have s1_5 : ((s + 1) / (s - 1)) ^ 3 = ((t + 1) / (t - 1)) ^ 3 := by
      calc ((s + 1) / (s - 1)) ^ 3 = f s := by exact (hH2 s hK1).symm
        _ = f t := by parley_set_side
        _ = ((t + 1) / (t - 1)) ^ 3 := by exact (hH2 t hK2)
    -- 1.6. thm:cube-injective a := (s + 1)/(s − 1), b := (t + 1)/(t − 1), from 1.5
    have s1_6 : (s + 1) / (s - 1) = (t + 1) / (t - 1) := by exact (Parley.Proofs.Hammack.CubeRootInjective.CubeInjective.cube_injective (a := (s + 1) / (s - 1)) (b := (t + 1) / (t - 1)) s1_5)
    -- 1.7. algebra, from 1.3, 1.4, 1.6
    linear_combination (norm := parley_field) (-((1 / 2 : ℝ) * s * t) + (1 / 2 : ℝ) * s + (1 / 2 : ℝ) * t - (1 / 2 : ℝ)) * s1_6
  -- 2. def:one-to-one, from H1, 1
  exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (f := f) hH1)).mpr ⟨hH1, s1⟩

end Parley.Proofs.Hammack.CubeRootInjective.CubedMobiusOneToOne
