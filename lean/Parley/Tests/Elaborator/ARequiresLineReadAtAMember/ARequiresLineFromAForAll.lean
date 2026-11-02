module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-line-read-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineReadAtAMember.ARequiresLineFromAForAll

theorem a_requires_line_from_a_for_all (n : ℕ) (hH1 : 0 < n) (hH2 : ∀ m : ℕ, 0 < m → (2 ^ m : ℤ) > 0) :
    (1 / 2 ^ n : ℚ) > 0 := by
  -- 1. mun:reciprocal-positive x := 2^n
  have r19_1 : (2 ^ n : ℤ) > 0 := by parley_side
  have s1 : (1 / 2 ^ n : ℚ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℚ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℚ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℚ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℚ)) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ARequiresLineReadAtAMember.ARequiresLineFromAForAll
