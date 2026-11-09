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
  the group's order, where the fact stands (`SuppliedBy`). It is one of: a
  line the citation names, a sentence or part of one, or what one implies
  (`Line`); one of the step's requires lines above the citing line, or what
  it implies (`Requires`); the `let` or `obtain` line that introduces a
  letter, for a membership said once (`SaidOnce`); or no line (`Unstated`).
  A hypothesis the citation's values make true is still placed where a line
  states it. Lean names that line as the item's argument.
- `Cited::firsts`: the line, or the sentence of one, a reading of a
  definition starts from, with the fact as the page writes it
  (`FirstAt::written`). Metamath unfolds the definition from it; Lean gives
  it to `.mp`, and to `.mpr` for the witnesses' facts.
- `FirstAt`: where a fact stands in a line. Its sentence is counted by its
  place among the sentences the line writes, from 0. Past those come the
  line's "for all" sentences read at a block's letter, in order. Its part is
  counted among the sentence's parts joined by "and". Where the line implies
  the fact rather than writing it, `implied` names the rule
  (`citing::Implication`). The rules are a range's bound, `k ≤ n` of
  `k ∈ {1, …, n}`; what ℕ or ℕ₀ says of a term, `n > 0` of `n ∈ ℕ`; a subset
  written as a power-set membership; and the others `implied_by` gives.
- `exhibited`: for each `exhibit` step, the values of each "there is" it
  shows, and where each fact it asks of them stands, placed as a citation's
  hypotheses are (`Exhibit::shown`). Both backends read the values; Lean
  also reads where the facts stand.
- `obtained_parts`: how each obtain step's sentences after its memberships
  are the parts of the "there is" it obtains from, and how each pair meets
  (`ObtainedPart`). Lean restates a part the checker met otherwise than as
  written.
- `instantiated`: for each instantiation, a step's, a calculation row's or a
  requires line's, three facts (`Instantiated`). The first is the sentence
  of the line instantiated (`FirstAt`). The second is how many conditions
  are taken off on the way to the claim. The third is how what is left meets
  the claim. Lean instantiates that sentence and closes the step by that
  meeting.
- `define_links`: for each calculation row citing a define, and each step
  whose reason is defines it names, how the two sides of its equation meet
  once the defines are written out. Lean closes it by `simp only [hD]`,
  adding `push_cast; norm_num` where that meeting or Lean's casts leave
  more.
- `links`: the relation each line a `transitivity` step cites gives its
  chain. Metamath reads it; Lean writes the chain by linear arithmetic.

## Blocks

- `blocks`: each block's owner, its steps, and what each part owes (`Owed`):
  the claim, what the last step ends on as the checks compare it (`ends`),
  and the same as the page writes it, the block's `let` and `assume` lines
  taken off (`written`). Metamath reads `ends`; Lean closes each part on
  `written`.
- `ends_met`: how each step that ends a block or the proof meets what it
  owes (`matching::Meeting`). The step may be turned round, have parts in
  another order or identity elements dropped, have bound letters renamed,
  or be respelled. Lean closes the block by the one tactic that meeting
  gives.
- `supposed`: how each contradiction's supposition stands to what it shows,
  by the line of the `suppose`: the claim negated, or the thing the claim
  negates, with what it is set against as written, and how the two meet.
  Lean opens the block by `by_contra` or by `intro` from it, turned where
  they meet turned.
- `contradicted`: for each step written `contradicting N` that ends a block
  or a case, where in line N the thing the step opposes stands (`FirstAt`).
  It also gives which of the two says the other negated, and how they meet.
  Lean closes the block on the pair.

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
