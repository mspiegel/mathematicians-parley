module

public import AlgebraTactics
public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/common-multiple-exists.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CommonMultipleExists.CommonMultipleExists

theorem common_multiple_exists (p : ℕ) (hH1 : 0 < p) (q : ℕ) (hH2 : 0 < q) :
    ¬ (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n} = ∅ := by
  -- 1. algebra
  have s1 : (p : ℤ) * (q : ℤ) * (p : ℤ) = (p : ℤ) * ((p : ℤ) * (q : ℤ)) := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ n : ℕ, 0 < n ∧ (p : ℤ) * (q : ℤ) * (p : ℤ) = (p : ℤ) * (n : ℤ) := ⟨p * q, by parley_set_side, by parley_set_side⟩
  -- 3. def:set-image u := (p·q)·p, from 2
  have s3 : (p : ℤ) * (q : ℤ) * (p : ℤ) ∈ (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (p : ℤ) * n)) (Y := {n : ℤ | 0 < n}) (u := (p : ℤ) * (q : ℤ) * (p : ℤ)) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (p : ℤ) * n)) (Y := {n : ℤ | 0 < n}) (u := (p : ℤ) * (q : ℤ) * (p : ℤ)) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
  -- 4. algebra
  have s4 : (p : ℤ) * (q : ℤ) * (p : ℤ) = (q : ℤ) * ((p : ℤ) * (p : ℤ)) := by parley_ring
  -- 5. exhibit, from 4
  have s5 : ∃ n : ℕ, 0 < n ∧ (p : ℤ) * (q : ℤ) * (p : ℤ) = (q : ℤ) * (n : ℤ) := ⟨p * p, by parley_set_side, by parley_set_side⟩
  -- 6. def:set-image u := (p·q)·p, from 5
  have s6 : (p : ℤ) * (q : ℤ) * (p : ℤ) ∈ (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (q : ℤ) * n)) (Y := {n : ℤ | 0 < n}) (u := (p : ℤ) * (q : ℤ) * (p : ℤ)) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (q : ℤ) * n)) (Y := {n : ℤ | 0 < n}) (u := (p : ℤ) * (q : ℤ) * (p : ℤ)) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
  -- 7. def:intersection u := (p·q)·p, from 3, 6
  have s7 : (p : ℤ) * (q : ℤ) * (p : ℤ) ∈ (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n}) (Z := (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n}) (u := (p : ℤ) * (q : ℤ) * (p : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n}) (Z := (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n}) (u := (p : ℤ) * (q : ℤ) * (p : ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 8. contradiction
  have s8 : ¬ (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n} = ∅ := by
    by_contra hc_hS
    have hS : (fun n : ℤ => (p : ℤ) * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => (q : ℤ) * n) '' {n : ℤ | 0 < n} = ∅ := by parley_suppose hc_hS
    -- 8.1. substitute {p·n : n ∈ ℕ} ∩ {q·n : n ∈ ℕ} = ∅ (S) into line 7
    have s8_1 : (p : ℤ) * (q : ℤ) * (p : ℤ) ∈ (∅ : Set ℤ) := by parley_subst_at hS s7
    -- 8.2. inspection
    have s8_2 : ¬ (p : ℤ) * (q : ℤ) * (p : ℤ) ∈ (∅ : Set ℤ) := by parley_set_side
    all_goals parley_set_side
  all_goals exact s8

end Parley.Proofs.Hammack.CommonMultipleExists.CommonMultipleExists
