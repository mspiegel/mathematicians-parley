module

public import Mathlib.Order.Filter.Defs
public import Lean.Parser.Command
public import Tactics

/-!
# A cited item's set given all of a number system or a range

An item that speaks of a set D states its hypotheses with D, `∀ x ∈ D, …`
or `D ∈ nhds x ∧ …` of a derivative within D. A citation that gives D all
of ℝ asks them with `Set.univ`, and one that gives D a range asks
`i ∈ Set.Icc a b`, where the citing proof's lines say `∀ x : ℝ, …` and
`i ∈ Finset.Icc a b`. The build writes `parley_whole_side` at exactly those
hypotheses and imports this module only where it does.
-/

public section

/-- A hypothesis of an item whose set a citation gives all of a number
system or a range: `parley_side`, or the line once `Set.univ` and the range
are read as the line reads them. -/
macro "parley_whole_side" : tactic =>
  `(tactic| first
    | (parley_side; done)
    | (simp only [Set.mem_univ, Filter.univ_mem, true_and, forall_const, true_implies] at *;
        assumption; done)
    | (simp only [Finset.coe_Icc, Finset.mem_Icc, Set.mem_Icc] at *;
        first | assumption | omega; done))

end
