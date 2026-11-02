module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.OddNotEven

theorem odd_not_even (n : ℤ) (hH2 : Odd n) :
    ¬ Even n := by
  -- 1. mun:divisibility-odd-not-even, from H2
  have s1 : ¬ Even n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.OddNotEven
