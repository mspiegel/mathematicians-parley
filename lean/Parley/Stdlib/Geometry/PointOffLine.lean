module

public import Geometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.OnLineOther

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.PointOffLine

theorem point_off_line (A : ℂ) (B : ℂ) (hH3 : A ≠ B) :
    (∃ O ∈ (Set.univ : Set ℂ), ¬ O ∈ LeanBridges.Geometry.line A B) := by
  -- 1. obtain U, V, W: axi:three-points
  obtain ⟨U, s1a, V, s1b, W, s1c, s1d⟩ := Parley.Items.Stdlib.Geometry.axi_three_points
  -- 2. mun:triangle-not-on-line P := U, Q := V, R := W, from 1
  have s2 : ¬ U ∈ LeanBridges.Geometry.line V W := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := U) (Q := V) (R := W) s1d)
  -- 3. axi:excluded-middle P := U is on line AB
  have s3 : U ∈ LeanBridges.Geometry.line A B ∨ ¬ U ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := U ∈ LeanBridges.Geometry.line A B))
  -- 4. cases, from 3
  rcases s3 with hC1 | hC6
  · skip
    -- 4.1. axi:excluded-middle P := V is on line AB
    have s4_1 : V ∈ LeanBridges.Geometry.line A B ∨ ¬ V ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := V ∈ LeanBridges.Geometry.line A B))
    -- 4.2. cases, from 4.1
    rcases s4_1 with hC2 | hC5
    · skip
      -- 4.2.1. axi:excluded-middle P := W is on line AB
      have s4_2_1 : W ∈ LeanBridges.Geometry.line A B ∨ ¬ W ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := W ∈ LeanBridges.Geometry.line A B))
      -- 4.2.2. cases, from 4.2.1
      rcases s4_2_1 with hC3 | hC4
      · skip
        -- 4.2.2.1. mun:on-line-other X := V, Y := W, Z := U, from C1, C2, C3, H3, 1
        have s4_2_2_1 : U ∈ LeanBridges.Geometry.line V W := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := A) (B := B) (X := V) (Y := W) (Z := U) hH3 s1d.2.1 hC2 hC3 hC1)
        -- 4.2.2.2. restate 2
        have s4_2_2_2 : ¬ U ∈ LeanBridges.Geometry.line V W := by exact s2
        exact absurd s4_2_2_1 s4_2_2_2
      · skip
        -- 4.2.2.3. exhibit, from C4
        exact ⟨W, Set.mem_univ _, hC4⟩
    · skip
      -- 4.2.3. exhibit, from C5
      exact ⟨V, Set.mem_univ _, hC5⟩
  · skip
    -- 4.3. exhibit, from C6
    exact ⟨U, Set.mem_univ _, hC6⟩

end Parley.Stdlib.Geometry.PointOffLine
