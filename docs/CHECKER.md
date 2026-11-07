# What the checker records

`parley check` reads each theorem once and keeps what it read as a
`CheckedTheorem` (`src/checker/record.rs`). Both backends build from that
record and not from the page (`GOALS.md` decision 19). Where a backend needs
a fact about a term, that it is an integer or that a set is finite, it takes
the fact from the record or from the page's lines, never from a reading of its
own (decision 20). A fact the record lacks is added here, for both backends,
and not inferred inside one.

## The reading

- `page`: every formula on the page, read once, which both backends write
  from.
- `items`: every sentence of every item the corpus may cite, read once for
  the corpus and shared by every theorem's record.
- `outside`, `statement_definitions`: the definitions the theorem sees,
  written out, which the statement is read with.
- `blocks`, `places`, `defines`: the proof's structure, where each step and
  each define stands.
- `sorts`: the sort of each name, as the theorem's one reading settles it.
- `problems`: what the checker reports. A backend builds a theorem only where
  this is empty.

## Citations

- `cited`, `cited_requires`: each step's and each requires line's citation,
  with the item, the group of its conclusions taken, and what each of its
  letters stands for. Both backends apply the item from this and do not match
  it again.
- `exhibited`: the values each `exhibit` step shows. Both read it.
- `links`: the relation each line a `transitivity` step cites gives its
  chain. Metamath reads it; Lean writes the chain by linear arithmetic.

## Facts about terms

- `introduced`: the number system each letter in scope at a step is
  introduced in, narrowed where a later line narrows it. Both read it,
  through the shared said-once rule (`citing::reason`), so that a membership
  one backend proves the other can too.
- `said_sums`: the sums each step writes that the page says are numbers
  once. Metamath proves their memberships from it.
- `said_finite`: the sets the hypotheses, defines and bound letters make
  finite, and for each hypothesis the sets only it does. Lean writes a count
  by it, `ncard` or `encard` (`citing::finite::is_finite`).
- `set_systems`: the number system each set letter of numbers holds. Lean
  types the letter by it.
- `typed`: the function types the lines in scope at each step say, which a
  citation of an item over a function is read with. Lean reads it.
- `asserted`, `opener_asserted`: what a `let` line asserts that the page does
  not read as a formula, such as `f : A → B be one-to-one`. Lean writes it as
  a hypothesis.
- `places_shown`: each term a step puts where a notation's definition asks a
  number system (both sides of a ≡, the places of "divides" and "is prime"),
  with how the step shows it is in that system: said once, or beside an
  equation a line the step names says. Lean proves the second from the
  equation and the other side's line, as the check found it.
- `members_shown`: the same of each claim the `membership` method proves
  whose term is in its system beside an equation, by the line its reason is
  on. Lean proves it the same way.
- `kind_letters`: the letters the reason under a function's define that says
  a kind of number is read with, the step's below the define and the define's
  argument in its domain. Lean proves the kind with them.
