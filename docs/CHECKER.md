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
- `Cited::supplied`: for each hypothesis of the group a citation takes, in
  the group's order, where the fact the search took for it stands: a line the
  citation names, a sentence or part of one, with the fact as the page writes
  it; one of the step's requires lines; or no line, a membership said once.
  Lean names that line as the item's argument.
- `Cited::firsts`: the line, or the sentence of one, a reading of a
  definition starts from, with the fact as the page writes it
  (`FirstAt::written`). Metamath unfolds the definition from it; Lean gives
  it to `.mp`, and to `.mpr` for the witnesses' facts.
- `exhibited`: the values each `exhibit` step shows. Both read it.
- `links`: the relation each line a `transitivity` step cites gives its
  chain. Metamath reads it; Lean writes the chain by linear arithmetic.

## Blocks

- `blocks`: each block's owner, its steps, and what each part owes (`Owed`):
  the claim, what the last step ends on as the checks compare it (`ends`),
  and the same as the page writes it, the block's `let` and `assume` lines
  taken off (`written`). Metamath reads `ends`; Lean closes each part on
  `written`.
- `supposed`: how each contradiction's supposition stands to what it shows,
  by the line of the `suppose`: the claim negated, or the thing the claim
  negates, with what it is set against as written. Lean opens the block by
  `by_contra` or by `intro` from it.
- `contradicted`: for each step written `contradicting N` that ends a block
  or a case, the line N, what of it the step opposes as the page writes it,
  and which of the two says the other negated. Lean closes the block on the
  pair.

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
- `held_by_lines`: the parts of the terms each reason writes, and of the
  lines it names, that those lines put in a number system, by the line the
  reason is on: a step's, a requires line's, or the reason under a define
  that says a kind. Each says how: a line states it, an equation puts it
  beside a term in the system, or the closure table puts it there. Lean
  names a part whole only from such a line, m of m² from `m ∈ ℕ` where the
  step names it, and never from a line the reason does not name.
- `read_at`: each "for all" a line a step may cite says that the step reads
  at the letter of a block around it, with that letter, by the step's index:
  "for all x ∈ ℝ, x < x + 1" read at the y of the block's `let y ∈ ℝ`. Lean
  reads a cited "for all" at that letter and at no other.
- `statement_bounds`, `bounds`: what the statement's hypotheses, and the
  lines in scope above each step, bound below, y − 3 ≥ 0 of `y ≥ 3` or
  x ≥ 1 of `x ∈ ℕ` (`citing::bounds`), read with the letters in scope.
  Lean writes a square root or a real power of a base at least 0 as a real
  one, as Metamath proves `√x ∈ ℝ` from `0 ≤ x`.
- `finite_at`: the sets the lines in scope above each step say are finite
  in words, `W is finite`, or a part of a finite set, `Y ⊆ X` or `Y ∈ 𝒫X`.
  Lean counts such a set as a natural number from that step on.
- `element_systems`: the number system each letter the page puts in sets
  of numbers is in, the widest of them, A of `A ∈ ℝ ∖ ℚ`. Lean gives `let A
  be an element` that type.
- `function_systems`: the function letters a line types between sets of
  numbers, f of `f : ℤ → ℝ`, with the systems of the domain and the
  codomain.
- `written`: the record with what the theorem's file defines outside it
  written out, T(k + 1) of `define T(k) := k(k + 1)/2` as (k + 1)(k + 2)/2,
  and each phrase as its meaning, its facts read again of the page as
  written. Lean, which has no name for such a function, reads this record.
- `item_facts`, of the library's reading rather than a theorem's: for each
  group of each item, what its hypotheses bound below and make finite, and
  for each sentence it concludes, the number systems of its set letters.
