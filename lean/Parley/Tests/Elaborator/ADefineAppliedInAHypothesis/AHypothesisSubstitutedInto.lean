module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-define-applied-in-a-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineAppliedInAHypothesis.AHypothesisSubstitutedInto

theorem a_hypothesis_substituted_into (m : ℕ) (hH1 : 0 < m) (n : ℕ) (hH2 : 0 < n) (hH3 : ({d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) - 1 + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ) - 1}.ncard : ℤ) * ((m : ℤ) - 1 + (n : ℤ)) = 0) :
    ({d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) - 1 + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ) - 1}.ncard : ℤ) * ((m : ℤ) + ((n : ℤ) - 1)) = 0 := by
  -- 1. mun:nat-minus-one n := m
  have s1 : 0 ≤ (m : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side)); parley_set_side)
  -- 2. algebra
  have s2 : (m : ℤ) - 1 + (n : ℤ) = (m : ℤ) + ((n : ℤ) - 1) := by parley_ring
  -- 3. substitute (m − 1) + n = m + (n − 1) (line 2) into H3
  have r21_1 : 0 ≤ (m : ℤ) - 1 := by parley_set_side
  have s3 : ({d ∈ 𝒫 (Set.Icc (1 : ℤ) ((m : ℤ) - 1 + (n : ℤ)) : Set ℤ) | (d.ncard : ℤ) = (m : ℤ) - 1}.ncard : ℤ) * ((m : ℤ) + ((n : ℤ) - 1)) = 0 := by parley_subst_at s2 hH3
  all_goals exact s3

end Parley.Tests.Elaborator.ADefineAppliedInAHypothesis.AHypothesisSubstitutedInto
