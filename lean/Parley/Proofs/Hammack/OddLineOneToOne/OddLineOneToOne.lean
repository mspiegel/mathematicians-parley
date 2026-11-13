module

public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/hammack/odd-line-one-to-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddLineOneToOne.OddLineOneToOne

theorem odd_line_one_to_one (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, f n = 2 * n + 1) :
    (Set.MapsTo f (Set.univ : Set ℤ) (Set.univ : Set ℤ) ∧ Set.InjOn f (Set.univ : Set ℤ)) := by
  -- 1. proof
  have s1 : ∀ s : ℤ, ∀ t : ℤ, f s = f t → s = t := by
    intro s
    intro t
    intro hA1
    -- 1.1. calculation
    have s1_1 : 2 * s + 1 = 2 * t + 1 := by
      calc 2 * s + 1 = f s := by exact (hH2 s).symm
        _ = f t := by parley_set_side
        _ = 2 * t + 1 := by exact (hH2 t)
    -- 1.2. algebra, from 1.1
    qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s1_1
  -- 2. def:one-to-one, from H1, 1
  exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (Set.mapsTo_univ _ _))).mpr ⟨Set.mapsTo_univ _ _, by simpa only [Set.mem_univ, forall_const] using s1⟩

end Parley.Proofs.Hammack.OddLineOneToOne.OddLineOneToOne
