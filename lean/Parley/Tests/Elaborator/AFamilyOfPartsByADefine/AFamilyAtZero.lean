module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyAtZero

theorem a_family_at_zero (m : ℕ) (hH1 : 0 < m) :
    {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + 0) : Set ℤ) | d.encard = ((m : ℕ) : ℕ∞)} | (1 : ℤ) ∈ c} ⊆ {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)} := by
  -- 1. mun:set-builder-subset X := {e ⊆ {1, …, m} : |e| = m}, from D1
  have s1 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + 0) : Set ℤ) | d.encard = ((m : ℕ) : ℕ∞)} | (1 : ℤ) ∈ c} ⊆ {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)} := by first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)})) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)})) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ) | e.encard = ((m : ℕ) : ℕ∞)})); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyAtZero
