module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Ballot.GoodFinite
public import Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.TieCount

theorem tie_count (m : ℕ) :
    ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * ((m : ℤ) + (m : ℤ)) = ((m : ℤ) - (m : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (m : ℤ)) (m : ℤ) : ℤ) := by
  -- 1. axi:excluded-middle P := m = 0
  have s1 : (m : ℤ) = 0 ∨ (m : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℤ) = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℤ) = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℤ) = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℤ) = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (m : ℤ) = 0)); parley_set_side)
  -- 2. cases, from 1
  have s2 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * ((m : ℤ) + (m : ℤ)) = ((m : ℤ) - (m : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (m : ℤ)) (m : ℤ) : ℤ) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. thm:good-finite n := m
      have s2_1 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by first | exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (n := m)) | exact ((Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (n := m))).symm | simpa using (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (n := m)) | exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (n := m)) | (have h := (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (n := m)); parley_set_side)
      -- 2.2. mun:card-nat0 X := G(m, m), from 2.1
      have s2_2 : 0 ≤ ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s2_1) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s2_1)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s2_1) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s2_1) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s2_1); parley_set_side)
      -- 2.3. calculation
      have s2_3 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * ((m : ℤ) + (m : ℤ)) = ((m : ℤ) - (m : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (m : ℤ)) (m : ℤ) : ℤ) := by
        calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * ((m : ℤ) + (m : ℤ)) = 0 := by linear_combination (norm := parley_norm) (2 * ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ)) * hC1
          _ = ((m : ℤ) - (m : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (m : ℤ)) (m : ℤ) : ℤ) := by parley_ring
      all_goals parley_set_side
    · skip
      -- 2.4. mun:nat0-nonzero, from C2
      have s2_4 : 0 < m := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_set_side)); parley_set_side)
      -- 2.5. thm:tie-at-the-end, from 2.4
      have s2_5 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} = ∅ := by first | exact (Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd.tie_at_the_end (m := m) (by parley_set_side)) | exact ((Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd.tie_at_the_end (m := m) (by parley_set_side))).symm | simpa using (Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd.tie_at_the_end (m := m) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd.tie_at_the_end (m := m) (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd.tie_at_the_end (m := m) (by parley_set_side)); parley_set_side)
      -- 2.6. calculation
      have s2_6 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 0 := by
        calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = ((∅ : Set (Set ℤ)).ncard : ℤ) := by parley_subst s2_5
          _ = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.mun_card_empty | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.mun_card_empty | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty).symm | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.mun_card_empty; parley_set_side)
      -- 2.7. calculation
      have s2_7 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * ((m : ℤ) + (m : ℤ)) = ((m : ℤ) - (m : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (m : ℤ)) (m : ℤ) : ℤ) := by
        calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) + (m : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ)} | ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (m : ℤ)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * ((m : ℤ) + (m : ℤ)) = 0 := by linear_combination (norm := parley_norm) (2 * (m : ℤ)) * s2_6
          _ = ((m : ℤ) - (m : ℤ)) * (LeanBridges.Counting.choose ((m : ℤ) + (m : ℤ)) (m : ℤ) : ℤ) := by parley_ring
      all_goals parley_set_side
  all_goals exact s2

end Parley.Proofs.Wiedijk.Ballot.TieCount
