module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.RationalClosure.RationalQuotient

/-! Written from proofs/setmm/irrational-times-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IrrationalTimesRational.IrrationalTimesRational

theorem irrational_times_rational (A : ℝ) (B : ℝ) (hH3 : A ∈ (Set.univ : Set ℝ) \ {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (B : ℚ) (hH5 : B ≠ 0) :
    A * (B : ℝ) ∈ (Set.univ : Set ℝ) \ {x : ℝ | ∃ m : ℚ, (m : ℝ) = x} := by
  -- 1. def:difference u := A, from H3
  have s1 : ¬ (∃ m : ℚ, (m : ℝ) = A) := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A))).mp (by parley_set_side)).2; parley_set_side)
  -- 2. membership, from 1
  -- 3. contradiction
  have s3 : ¬ (∃ m : ℚ, (m : ℝ) = A * (B : ℝ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = A * (B : ℝ) := by parley_suppose hc_hS
    -- 3.1. thm:rational-quotient A := A·B, from H4, H5, S
    have s3_1 : ∃ m : ℚ, (m : ℝ) = A * (B : ℝ) / (B : ℝ) := by (exact ⟨(Classical.choose hS) / B, by push_cast; (try simp only [Classical.choose_spec hS]); first | done | parley_ring⟩)
    -- 3.2. substitute
    have s3_2 : ∃ m : ℚ, (m : ℝ) = A := by
      have c1 : A * (B : ℝ) / (B : ℝ) = A := by parley_ring
      have row1 : ∃ m : ℚ, (m : ℝ) = A := by parley_subst_at c1 s3_1
      exact row1
    -- 3.3. restate 1
    have s3_3 : ¬ (∃ m : ℚ, (m : ℝ) = A) := by parley_set_side
    all_goals parley_set_side
  -- 4. def:difference u := A·B, from 2, 3
  have s4 : A * (B : ℝ) ∈ (Set.univ : Set ℝ) \ {x : ℝ | ∃ m : ℚ, (m : ℝ) = x} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A * (B : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A * (B : ℝ)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s4

end Parley.Proofs.Setmm.IrrationalTimesRational.IrrationalTimesRational
