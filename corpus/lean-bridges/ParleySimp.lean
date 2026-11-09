module

public import Lean.Parser.Command
public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The simp set the tactics unfold definitions with

`parley_unfold` is empty here. A module of definitions the tactics must see
through tags them into it (`FactorialTactics` tags the factorial and the
binomial coefficient), and a file importing that module has them in the
set; any other file has none. The tactics call `norm_num [parley_unfold]`
and `field_simp [parley_unfold]` at the place in their lists those ways
belong, so the core tactics never import the definitions themselves. A set
must be declared in a module before the one that uses it, so it is here,
apart from `Tactics`.
-/

public section

/-- The definitions the tactics see through, where a module tags them. -/
register_simp_attr parley_unfold

/-- The facts that join an item's Lean statement, written once over any ring
or set, to the step's spelling of it at a citation's values, each one
representation fact (`InstanceTactics`). -/
register_simp_attr parley_spelling

end
