module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/substitute-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SubstituteRows.SubstituteRows

theorem substitute_rows (n : ℤ) (d : ℤ) (hH3 : d ∣ n + 1) (hH4 : d ∣ n) :
    d ∣ (1 : ℤ) := by
  -- 1. mun:divides-difference a := n + 1, b := n, from H3, H4
  have s1 : d ∣ n + 1 - n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) (by parley_side) (by parley_side)); parley_side)
  -- 2. substitute
  have s2 : d ∣ (1 : ℤ) := by
    have c1 : n + 1 - n = 1 := by parley_ring
    have row1 : d ∣ (1 : ℤ) := by parley_subst_at c1 s1
    exact row1
  all_goals parley_side

end Parley.Tests.Elaborator.SubstituteRows.SubstituteRows
