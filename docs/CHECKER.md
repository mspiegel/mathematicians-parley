# What the checker records

`parley check` reads each theorem once and keeps what it read as a
`CheckedTheorem` (`src/checker/record.rs`). Both backends build from that
record and not from the page (`GOALS.md` decision 19). Where a backend needs
a fact about a term, that it is an integer or that a set is finite, it takes
the fact from the record or from the page's lines, never from a reading of its
own (decision 20). A fact the record lacks is added here, for both backends,
and not inferred inside one.

`parley check` and both builds start with one run of the checker
(`checker::front`). It reads the corpus, makes every check `parley check`
reports, and makes the record of every theorem, the library's item facts
and the records as the page is written out. `parley check` prints what it
reports; a build prints the same, then builds from the record. So every
reading a backend uses runs under `parley check`, and a build refuses
exactly what the check refuses.

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
  Each concluded sentence also records, where the item's reading is an
  "and", which part of it met the claim's sentence (`Concluded::part`),
  counted from 0 left to right with every conjunction taken apart. Lean
  takes that part of the reading by its projection.
- `Cited::supplied`: for each hypothesis of the group a citation takes, in
  the group's order, where the fact stands (`SuppliedBy`). It is one of: a
  line the citation names, a sentence or part of one, or what one implies
  (`Line`); one of the step's requires lines above the citing line, or what
  it implies (`Requires`); the `let` or `obtain` line that introduces a
  letter, for a membership said once (`SaidOnce`); or no line (`Unstated`).
  A hypothesis the citation's values make true is still placed where a line
  states it. Lean names that line as the item's argument.
- `Cited::item_letters`: for each letter of a cited item the binding fills,
  the Parley number system the item takes it in, by its own hypothesis
  `x ∈ S`, and the narrowest the page says its value is in once
  (`citing::within`). For `mun:abs-nonneg x := C` with C real: x in ℂ, from
  ℝ. A letter that stands for a set, given a number system as its value,
  `X := ℕ` or `D := ℝ`, records that system as the set it is
  (`ItemLetter::value_set`).
- `Cited::facings`: for each conclusion a citation takes, whether the item's
  equation, read at the citation's values, meets the claim's equation
  straight or turned round.
- `Cited::meetings`: for each conclusion a citation takes, how the item's
  sentence, read at the citation's values, met the claim's
  (`Known::alike_how`), with the identity elements dropped on the way, x − 0
  read as x. Lean rewrites by those identities (`sub_zero`, `zero_add`, …)
  where it converts a power at the step.
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
  written. Each pairing carries the body's part as the checker read it
  (`owed_written`), since the checker counts parts as the page writes them.
- `instantiated`: for each instantiation, a step's, a calculation row's or a
  requires line's, three facts (`Instantiated`). The first is the sentence
  of the line instantiated (`FirstAt`). The second is how many conditions
  are taken off on the way to the claim. The third is how what is left meets
  the claim. Lean instantiates that sentence and closes the step by that
  meeting.
- `link_places`: for each link of a calculation that cites a line, where in
  the line the link stands (`FirstAt`), by the link's line. A link read off
  a chain, `a = c` of `a = b = c`, stands at the chain's sentence, with the
  pair as `written`.
- `link_facings`: for each link of a calculation that cites a line, which
  way it faces what the line says, `Straight` or `Turned`, compared as a
  citation's facing is (`citations::facing_of`), by the link's line. Lean
  uses the line as it stands or turned round, `linear_combination line` or
  `-line`, `exact` or `.symm`.
- `substituted`: for each `substitute` step and calculation row that
  writes no rows, how its substitution makes the claim (`Substituted`), by
  its line. It holds the equation as the page writes it, and where the line
  it is taken from says it (`FirstAt`), or nothing for a written equation
  from a define or arithmetic. It holds what the equation is put into: a
  fact of the line the step names (`FirstAt`), or a side of the claim
  `t = t′`. And it holds where it is put: which way round, and each place
  by its path in the trees as the page writes them. Lean writes what the
  equation is put into with those places as one letter, and closes the
  step by `Eq.subst` along it. Where the putting leaves identity elements
  the claim drops, `1·x` written `x`, it holds those (`identities`), the
  equation put at every place its side stands. A substitution found only in
  the standard order is not recorded, and the step keeps its ways.
- `substituted_rows`: for each row of a `substitute` step after the first,
  how its change, which its reason proves, goes into the row above
  (`SubstitutedInto::RowAbove`), by the line of the row's reason; places as
  in `substituted`. It is kept apart from `substituted`, which has under
  that line how the reason itself makes the change.
- `define_links`: for each calculation row citing a define, and each step
  whose reason is defines it names, how the two sides of its equation meet
  once the defines are written out, or that they do not meet and arithmetic
  is left (`None`). A claim "for all x ∈ S, A = B" is read at its body.
  Lean closes it by `simp only [hD]`, adding `push_cast; norm_num` where
  that meeting, arithmetic left, or Lean's casts ask more.
- `define_cases`: for each step citing a define by cases whose value it
  claims in one case, the conditions it passes to reach that case, in the
  define's order. Each condition holds, for the case it gives, or fails,
  for the cases after it, with where a line the step cites says so
  (`FirstAt`). It also records how the case's value meets the claim's other
  side. The check that the step's claim is the define's value reads the
  step the same way (`value_given`). Lean puts each condition by
  `if_pos h` or `if_neg h`, h that line.
- `define_domains`: for each step citing a function a define lets on a
  domain, where a line the step cites says the argument its claim applies
  the function at is in that domain (`FirstAt`). Lean puts the function's
  equation at that argument, `hD1 _ h`, h that line, which `simp` would
  otherwise have to show.
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
- `said_finite`: the sets the theorem's hypotheses, defines and bound
  letters make finite, each with why (`citing::finite::FiniteBy`): a line
  says so, a line gives its count as a number (|Y| = 2), a part of a
  finite set by the line `B ⊆ A`, a define, or a letter
  bound only over sets of finite sets; and, per hypothesis, the sets only it
  makes finite, since a line giving a count that may be 0 cannot vouch for
  itself. Whether any other set
  is finite, and why, is `citing::finite::finite_by` over these: ∅, a listed
  set, a range, and A ∖ B, A ∩ B, A ∪ B, 𝒫A, a set-builder or an image of
  finite parts. Every backend asks that one function, and none decides it
  for itself.
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
  x ≥ 1 of `x ∈ ℕ` (`citing::bounds`), read with the letters in scope,
  each with the sentence that says it (`Bound::said_by`). Lean writes a
  square root or a real power of a base at least 0 as a real one, as
  Metamath proves `√x ∈ ℝ` from `0 ≤ x`. Where Lean converts a power, it
  proves the exponent at least 0 from that sentence.
- `finite_at`: for each step, the sets the lines in scope make finite,
  `W is finite`, `|W| = m`, or `B ⊆ A` of a finite A, each with why, as
  `said_finite` keeps them. A count records whether its number is at least
  1 by the step's bounds, which says whether its line is written
  `W.ncard = 2` or `W.encard = m`, and so how a backend proves W finite
  from it.
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
