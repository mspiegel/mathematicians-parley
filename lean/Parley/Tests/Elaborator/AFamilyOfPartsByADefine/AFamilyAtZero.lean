module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyAtZero

theorem a_family_at_zero (m : ℤ) (hH1 : 0 < m) :
    {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | (1 : ℤ) ∈ c} ⊆ {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (e.ncard : ℤ) = m} := by
  -- 1. mun:set-builder-subset X := {e ⊆ {1, …, m} : |e| = m}, from D1
  first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (e.ncard : ℤ) = m})) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (e.ncard : ℤ) = m}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (e.ncard : ℤ) = m})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (e.ncard : ℤ) = m})) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (e.ncard : ℤ) = m})); parley_set_side)

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyAtZero
