module

public import Lean.Parser.Command
public import Factorials
public import Counting
public import Divisibility
public import Numbers
public import Sums
public import PowerTactics
public import Logarithms
public import Calculus
public import Functions
public import Sets
public import Groups
public import Graphs
public import Polynomials
public import ZF

/-!
# The bridges a generated proof uses

The definitions a page's notations stand for where Mathlib has none, and
lemmas a generated proof cites, each stating one fact: a natural number
given as an integer's `toNat` (`PowerTactics`), the bounds of a logarithm
(`Logarithms`), a product or sum over a range as a set (`Sums`). The
bridges define no tactic: a generated proof calls Lean's and Mathlib's
own, chosen by the writer, and nothing that decides its way at proof
time.

Lean rebuilds every file that imports a module, directly or through
another, whenever that module changes, so each module is imported only by
the files that name one of its lemmas or definitions. Which file imports
which module is decided by the build from the constants the file's trees
name (`modules_of` in `src/tools/build/lean.rs`), and which Mathlib
modules it imports from the table Lean makes of them
(`src/lean/modules.rs`).
-/
