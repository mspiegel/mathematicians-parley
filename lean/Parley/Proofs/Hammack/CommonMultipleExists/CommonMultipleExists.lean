module

public import AlgebraTactics
public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/common-multiple-exists.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CommonMultipleExists.CommonMultipleExists

theorem common_multiple_exists (p : ℤ) (hH1 : 0 < p) (q : ℤ) (hH2 : 0 < q) :
    ¬ (fun n : ℤ => p * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => q * n) '' {n : ℤ | 0 < n} = ∅ := by
  -- 1. algebra
  have s1 : p * q * p = p * (p * q) := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ n : ℤ, 0 < n ∧ p * q * p = p * n := ⟨p * q, by parley_set_side, by parley_set_side⟩
  -- 3. def:set-image u := (p·q)·p, from 2
  have s3 : p * q * p ∈ (fun n : ℤ => p * n) '' {n : ℤ | 0 < n} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => p * n)) (Y := {n : ℤ | 0 < n}) (u := p * q * p) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => p * n)) (Y := {n : ℤ | 0 < n}) (u := p * q * p) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 4. algebra
  have s4 : p * q * p = q * (p * p) := by parley_ring
  -- 5. exhibit, from 4
  have s5 : ∃ n : ℤ, 0 < n ∧ p * q * p = q * n := ⟨p * p, by parley_set_side, by parley_set_side⟩
  -- 6. def:set-image u := (p·q)·p, from 5
  have s6 : p * q * p ∈ (fun n : ℤ => q * n) '' {n : ℤ | 0 < n} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => q * n)) (Y := {n : ℤ | 0 < n}) (u := p * q * p) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => q * n)) (Y := {n : ℤ | 0 < n}) (u := p * q * p) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 7. def:intersection u := (p·q)·p, from 3, 6
  have s7 : p * q * p ∈ (fun n : ℤ => p * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => q * n) '' {n : ℤ | 0 < n} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => p * n) '' {n : ℤ | 0 < n}) (Z := (fun n : ℤ => q * n) '' {n : ℤ | 0 < n}) (u := p * q * p))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := (fun n : ℤ => p * n) '' {n : ℤ | 0 < n}) (Z := (fun n : ℤ => q * n) '' {n : ℤ | 0 < n}) (u := p * q * p))).mpr (by parley_set_side); parley_set_side)
  -- 8. contradiction
  have s8 : ¬ (fun n : ℤ => p * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => q * n) '' {n : ℤ | 0 < n} = ∅ := by
    by_contra hc_hS
    have hS : (fun n : ℤ => p * n) '' {n : ℤ | 0 < n} ∩ (fun n : ℤ => q * n) '' {n : ℤ | 0 < n} = ∅ := by parley_suppose hc_hS
    -- 8.1. substitute {p·n : n ∈ ℕ} ∩ {q·n : n ∈ ℕ} = ∅ (S) into line 7
    have s8_1 : p * q * p ∈ (∅ : Set ℤ) := by parley_subst_at hS s7
    -- 8.2. inspection
    have s8_2 : ¬ p * q * p ∈ (∅ : Set ℤ) := by parley_set_side
    all_goals parley_set_side
  all_goals exact s8

end Parley.Proofs.Hammack.CommonMultipleExists.CommonMultipleExists
