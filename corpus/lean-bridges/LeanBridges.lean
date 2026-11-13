module

public import Lean.Parser.Command
public import Factorials
public import Counting
public import Divisibility
public import Numbers
public import Sums
public import NormTactics
public import SetTactics
public import Roots
public import RealTactics
public import Calculus
public import Functions
public import Sets
public import Groups
public import Polynomials

/-!
# The bridges a generated proof uses

The definitions a page's notations stand for where Mathlib has none, and
the tactics a generated proof calls. Each tactic closes a goal of one kind
and is named for that kind, so a generated proof says what it asks and the
search for how is written once. Every alternative closes the goal or
fails: `ring`, `norm_num` and `apply` can succeed while leaving a goal
open, so each alternative ends in `done`, and `ring1` is used for `ring`.

## How the tactic modules are laid out

Lean rebuilds every file that imports a module, directly or through
another, whenever that module changes. The layout keeps each change's
rebuild to the files that use what changed.

- Each family of tactics is a module of its own, imported only by the
  files that name one of its tactics: `NormTactics`, `AlgebraTactics`,
  `SubstTactics`, `PowerTactics`, `InstanceTactics`, `ComplexTactics`,
  `ArithTactics`, `SetTactics`, `RealTactics`.
- A module imports the whole family of each Mathlib tactic it calls,
  `Mathlib.Tactic.NormNum` for `norm_num`, so that the tactic has every
  extension a goal may need wherever it runs.
- A definition only some files write, which a tactic must see through, is
  not imported by the tactic's module. The tactic calls `norm_num` or
  `field_simp` with the simp set `parley_unfold` (`ParleySimp`, which
  imports only Lean) at the place in its list that way belongs, and a
  module imported only by the files that write the definition tags it
  into the set. Elsewhere the set is empty and the call is a plain one.
  The factorial and the binomial coefficient are tagged so, in
  `FactorialTactics`, and a change to `Factorials` rebuilds only the files
  that write them. A `macro_rules` rule for the tactic would be tried
  before its own alternatives, and a hook with a default would be tried
  again after the rule failed; the set changes neither the order nor the
  number of tries.
- A case for a goal the writer can recognise where it writes the call goes
  in a tactic of its own with its own name, rather than among another
  tactic's alternatives.

Which file imports which module is decided by the build from the tactics
and constants the file's trees name (`modules_of` in
`src/tools/build/lean.rs`), and which Mathlib modules it imports from the
table Lean makes of them (`src/lean/modules.rs`).
-/
