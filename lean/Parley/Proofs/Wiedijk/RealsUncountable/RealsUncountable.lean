module

public import ArithTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Functions
public import Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.RealsUncountable

theorem reals_uncountable :
    ¬ (∃ g : ℤ → ℝ, Set.BijOn g {n : ℤ | 0 < n} (Set.univ : Set ℝ)) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ g : ℤ → ℝ, Set.BijOn g {n : ℤ | 0 < n} (Set.univ : Set ℝ)) := by
    by_contra hc_hS
    have hS : ∃ g : ℤ → ℝ, Set.BijOn g {n : ℤ | 0 < n} (Set.univ : Set ℝ) := by parley_suppose hc_hS
    -- 1. obtain f: mun:bijection-onto X := ℕ, Y := ℝ, from S
    obtain ⟨f, _, s1⟩ := (Parley.Items.Stdlib.Functions.mun_bijection_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (by parley_whole_side))
    -- 2. def:onto, from 1
    have s2 : ∀ y : ℝ, ∃ n : ℤ, 0 < n ∧ y = f n := by first | exact ((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mp (by parley_set_side); parley_set_side)
    -- 3. obtain x: thm:sequence-misses-real
    obtain ⟨x, s3⟩ := (Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal.sequence_misses_real (f := f))
    -- 4. instantiate y := x in line 2
    have s4 : ∃ n : ℤ, 0 < n ∧ x = f n := by first | exact (s2 x) | exact ((s2 x)).symm | simpa using (s2 x) | exact_mod_cast (s2 x) | (have h := (s2 x); parley_set_side)
    -- 5. obtain m from line 4
    obtain ⟨m, s5a, s5b⟩ := s4
    -- 6. instantiate n := m in line 3
    have s6 : x ≠ f m := by first | exact (s3 m (by parley_set_side)) | exact ((s3 m (by parley_set_side))).symm | simpa using (s3 m (by parley_set_side)) | exact_mod_cast (s3 m (by parley_set_side)) | (have h := (s3 m (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Wiedijk.RealsUncountable.RealsUncountable
