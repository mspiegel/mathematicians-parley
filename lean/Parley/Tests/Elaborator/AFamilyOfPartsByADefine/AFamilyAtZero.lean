module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyAtZero

theorem a_family_at_zero (m : ℤ) (hH1 : 0 < m) :
    {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | d.encard = ((m.toNat : ℕ) : ℕ∞)} | (1 : ℤ) ∈ c} ⊆ {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)} := by
  -- 1. mun:set-builder-subset X := {e ⊆ {1, …, m} : |e| = m}, from D1
  have s1 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | d.encard = ((m.toNat : ℕ) : ℕ∞)} | (1 : ℤ) ∈ c} ⊆ {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)} := by first | exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)})) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)}))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)})) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)})) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)})); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)})); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => (1 : ℤ) ∈ c)) (X := {e ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | e.encard = ((m.toNat : ℕ) : ℕ∞)})); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AFamilyAtZero
