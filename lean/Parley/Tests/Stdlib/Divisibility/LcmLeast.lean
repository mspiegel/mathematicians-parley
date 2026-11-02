module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.LcmLeast

theorem lcm_least (a : ℤ) (b : ℤ) :
    (∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k) := by
  -- 1. def:lcm
  have s1 : ∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k := by first | exact (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.LcmLeast
