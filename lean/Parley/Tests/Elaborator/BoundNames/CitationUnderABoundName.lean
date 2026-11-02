module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/bound-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundNames.CitationUnderABoundName

theorem citation_under_a_bound_name (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (hH3 : ∀ e : ℕ, 0 < e → (e : ℤ) ≤ (e : ℤ)) :
    (∀ e : ℕ, 0 < e → (e : ℤ) ∣ (a : ℤ) ∧ (e : ℤ) ∣ (b : ℤ) → (e : ℤ) ≤ (Int.gcd (a : ℤ) (b : ℤ) : ℤ)) := by
  -- 1. def:gcd
  have s1 : ∀ e : ℕ, 0 < e → (e : ℤ) ∣ (a : ℤ) ∧ (e : ℤ) ∣ (b : ℤ) → (e : ℤ) ≤ (Int.gcd (a : ℤ) (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := a) (by parley_side) (b := b) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.BoundNames.CitationUnderABoundName
