module

public import OrderTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/squeeze-for-limits.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SqueezeForLimits.SqueezeForLimits

theorem squeeze_for_limits (f : ℝ → ℝ) (g : ℝ → ℝ) (h : ℝ → ℝ) (c : ℝ) (L : ℝ) (hH6 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → g x ≤ f x ∧ f x ≤ h x)) (hH7 : Filter.Tendsto g (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L)) (hH8 : Filter.Tendsto h (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L)) :
    Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:limit-at D := ℝ, f := g, from H7
    have r29_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (g x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := g) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := g) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := g) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := g) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := g) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 1.2. def:limit-at D := ℝ, f := h, from H8
    have r33_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
    have s1_2 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (h x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := h) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := h) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := h) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := h) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := h) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 1.3. instantiate ε := ε in line 1.1, from A1
    have s1_3 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (g x - L) < ε) := by first | exact (s1_1 ε (by parley_set_side)) | exact ((s1_1 ε (by parley_set_side))).symm | simpa using (s1_1 ε (by parley_set_side)) | exact_mod_cast (s1_1 ε (by parley_set_side)) | (have h := (s1_1 ε (by parley_set_side)); parley_set_side)
    -- 1.4. instantiate ε := ε in line 1.2, from A1
    have s1_4 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (h x - L) < ε) := by first | exact (s1_2 ε (by parley_set_side)) | exact ((s1_2 ε (by parley_set_side))).symm | simpa using (s1_2 ε (by parley_set_side)) | exact_mod_cast (s1_2 ε (by parley_set_side)) | (have h := (s1_2 ε (by parley_set_side)); parley_set_side)
    -- 1.5. obtain p from H6
    obtain ⟨p, ⟨s1_5a, s1_5b⟩⟩ := hH6
    -- 1.6. obtain q from line 1.3
    obtain ⟨q, ⟨s1_6a, s1_6b⟩⟩ := s1_3
    -- 1.7. obtain r from line 1.4
    obtain ⟨r, ⟨s1_7a, s1_7b⟩⟩ := s1_4
    set m : ℝ := min p q with hD1
    set n : ℝ := min m r with hD2
    -- 1.8. mun:lt-min z := 0, x := p, y := q, from 1.5, 1.6
    have s1_8 : 0 < min p q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := p) (y := q))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := p) (y := q))).mpr (by parley_set_side); parley_set_side)
    -- 1.9. inequalities, from D1, 1.8
    have s1_9 : 0 < m := by parley_order
    -- 1.10. mun:lt-min z := 0, x := m, y := r, from 1.7, 1.9
    have s1_10 : 0 < min m r := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := m) (y := r))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := m) (y := r))).mpr (by parley_set_side); parley_set_side)
    -- 1.11. inequalities, from D2, 1.10
    have s1_11 : n > 0 := by parley_order
    -- 1.12. proof
    have s1_12 : ∀ x : ℝ, x ≠ c ∧ abs (x - c) < n → abs (f x - L) < ε := by
      intro x
      intro hA2
      -- 1.12.1. mun:lt-min z := |x − c|, x := m, y := r, from A2, D2
      have s1_12_1 : abs (x - c) < m ∧ abs (x - c) < r := by
        try simp only [hD2] at *
        try push_cast at *
        first | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := m) (y := r))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := m) (y := r))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := m) (y := r))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := m) (y := r))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := m) (y := r))).mp (by parley_set_side); parley_set_side)
      -- 1.12.2. mun:lt-min z := |x − c|, x := p, y := q, from D1, 1.12.1
      have s1_12_2 : abs (x - c) < p ∧ abs (x - c) < q := by
        try simp only [hD1] at *
        try push_cast at *
        first | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := p) (y := q))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := p) (y := q))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := p) (y := q))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := p) (y := q))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - c)) (x := p) (y := q))).mp (by parley_set_side); parley_set_side)
      -- 1.12.3. join A2, 1.12.2
      have s1_12_3 : x ≠ c ∧ abs (x - c) < p := by parley_set_side
      -- 1.12.4. join A2, 1.12.2
      have s1_12_4 : x ≠ c ∧ abs (x - c) < q := by parley_set_side
      -- 1.12.5. join A2, 1.12.1
      have s1_12_5 : x ≠ c ∧ abs (x - c) < r := by parley_set_side
      -- 1.12.6. instantiate x := x in line 1.5, from 1.12.3
      have s1_12_6 : g x ≤ f x ∧ f x ≤ h x := by first | exact (s1_5b x (by parley_set_side)) | exact ((s1_5b x (by parley_set_side))).symm | simpa using (s1_5b x (by parley_set_side)) | exact_mod_cast (s1_5b x (by parley_set_side)) | (have h := (s1_5b x (by parley_set_side)); parley_set_side)
      -- 1.12.7. instantiate x := x in line 1.6, from 1.12.4
      have s1_12_7 : abs (g x - L) < ε := by first | linarith [(s1_6b x (by parley_set_side))] | (have h := (s1_6b x (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s1_6b x (by parley_set_side)) | (have h := (s1_6b x (by parley_set_side)); parley_set_side)
      -- 1.12.8. instantiate x := x in line 1.7, from 1.12.5
      have s1_12_8 : abs (h x - L) < ε := by first | linarith [(s1_7b x (by parley_set_side))] | (have h := (s1_7b x (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s1_7b x (by parley_set_side)) | (have h := (s1_7b x (by parley_set_side)); parley_set_side)
      -- 1.12.9. mun:abs-difference-lt x := g(x), c := L, δ := ε, from 1.12.7
      have s1_12_9 : L - ε < g x := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := g x) (c := L) (δ := ε))).mp (by parley_set_side)).1] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := g x) (c := L) (δ := ε))).mp (by parley_set_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := g x) (c := L) (δ := ε))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := g x) (c := L) (δ := ε))).mp (by parley_set_side)).1; parley_set_side)
      -- 1.12.10. mun:abs-difference-lt x := h(x), c := L, δ := ε, from 1.12.8
      have s1_12_10 : h x < L + ε := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := h x) (c := L) (δ := ε))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := h x) (c := L) (δ := ε))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := h x) (c := L) (δ := ε))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := h x) (c := L) (δ := ε))).mp (by parley_set_side)).2; parley_set_side)
      -- 1.12.11. transitivity, from 1.12.9, 1.12.6
      have s1_12_11 : L - ε < f x := by parley_order
      -- 1.12.12. transitivity, from 1.12.6, 1.12.10
      have s1_12_12 : f x < L + ε := by parley_order
      -- 1.12.13. join 1.12.11, 1.12.12
      have s1_12_13 : L - ε < f x ∧ f x < L + ε := by parley_set_side
      -- 1.12.14. mun:abs-difference-lt x := f(x), c := L, δ := ε, from 1.12.13
      have s1_12_14 : abs (f x - L) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := L) (δ := ε))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := L) (δ := ε))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    -- 1.13. exhibit, from 1.11, 1.12
    have s1_13 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε) := ⟨n, ⟨by parley_set_side, by parley_set_side⟩⟩
    all_goals parley_set_side
  -- 2. def:limit-at D := ℝ, from 1
  have r129_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  have s2 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_set_side) (c := c) (L := L) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SqueezeForLimits.SqueezeForLimits
