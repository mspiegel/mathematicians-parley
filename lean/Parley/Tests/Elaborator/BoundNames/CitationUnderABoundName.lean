module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/bound-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundNames.CitationUnderABoundName

theorem citation_under_a_bound_name (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (hH3 : ∀ e : ℤ, 0 < e → e ≤ e) :
    (∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ)) := by
  -- 1. def:gcd
  have s1 : ∀ e : ℤ, 0 < e → e ∣ a ∧ e ∣ b → e ≤ (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.BoundNames.CitationUnderABoundName
