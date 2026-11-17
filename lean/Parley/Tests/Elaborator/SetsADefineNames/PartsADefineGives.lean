module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.PartsADefineGives

theorem parts_a_define_gives (N : ℤ) (hH1 : 0 < N) (hH2 : N ∈ Finset.Icc (1 : ℤ) N) (V : ℤ → Set (Set ℤ)) (hD1 : ∀ k : ℤ, k ∈ Finset.Icc (1 : ℤ) N → V k = {S ∈ 𝒫 (Set.Icc (1 : ℤ) k : Set ℤ) | k ∈ S}) :
    ({N} : Set ℤ) ∈ V N := by
  -- 1. mun:singleton-subset, from H2
  have s1 : ({N} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (a := N) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hH2))
  -- 2. def:singleton x := N, a := N
  have s2 : N ∈ ({N} : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_singleton (a := N) (x := N))).mpr rfl
  -- 3. def:part-builder u := {N}, from D1, H2, 1, 2
  rw [hD1 _ hH2]
  exact ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S)) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := ({N} : Set ℤ)))).mpr ⟨s1, s2⟩

end Parley.Tests.Elaborator.SetsADefineNames.PartsADefineGives
