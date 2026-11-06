module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-line-read-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineReadAtAMember.ARequiresLineFromAForAll

theorem a_requires_line_from_a_for_all (n : ℤ) (hH1 : 0 < n) (hH2 : ∀ m : ℤ, 0 < m → (2 ^ m.toNat : ℤ) > 0) :
    (1 / 2 ^ n.toNat : ℚ) > 0 := by
  -- 1. mun:reciprocal-positive x := 2^n
  have r19_1 : (2 ^ n.toNat : ℤ) > 0 := by parley_side
  have s1 : (1 / 2 ^ n.toNat : ℚ) > 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n.toNat : ℚ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ARequiresLineReadAtAMember.ARequiresLineFromAForAll
