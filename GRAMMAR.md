# Grammar of the skeleton

`SYNTAX.md` says what a step must contain and why each form was chosen.
`DATABASE.md` says where things are stored. This document says how the stored
text is read: the line kinds, the justification forms, and the rules a parser
applies. It is written from the ten proofs in `proof/` and the three database
files in `db/`, and every rule below holds on all of them.

It covers the **skeleton only**. A claim is an opaque run of text here. Giving
that text structure is a second grammar, for notation and precedence, which is
not written and not needed to check anything in this document.

Every production below is checked against the corpus. All 246 justifications
match a declared production, all 22 labels match their pattern, the only part
markers are the three declared, and no step is numbered under a parent that
does not exist.

Notation used below: `<x>` a named part, `[x]` optional, `{x}` zero or more,
`a | b` alternatives. Literal text is in `code`.

## Lexical rules

Files are UTF-8 in Normalisation Form C. An implementation works in Unicode
scalar values; UTF-16 is used nowhere, for the reason in `DATABASE.md`. Every
non-ASCII character in a claim must appear in `db/notation.db`, which doubles
as a whitelist, with one addition: a variable may be a Greek letter and may
carry a subscript or a prime, as δ, ε, x₀ and P′ do. Those are how a name is
spelled rather than notation, so they have no record of their own and are
listed in the checker instead.

- `<label>` is `[A-Z]+[0-9]*`, written in parentheses at the end of the
  declaration and cited bare. Observed: H1, S, K2, IH, C1, D1. When the
  declaration is continued over several lines the label sits at the end of the
  last of them, as the eleventh hypothesis of the Bezout lemma does, so labels
  cannot be collected without applying the continuation rule first.
- `<number>` is a step number: one or more integers joined by dots, `1`,
  `1.1`, `17.25.5.10`.
- `<ref>` is a `<number>` or a `<label>`.
- `<name>` is `[A-Za-z][A-Za-z0-9-]*`, as in `least-upper-bound` and
  `nat0-closure`. The capital is in the pattern for `def:S` and `def:G`, the
  two items that take the letter of the function they define. Every other name
  is lowercase words joined by hyphens.
- `<term>` and `<formula>` are opaque runs of text, delimited only by the rules
  below. The parser does not look inside them.

Horizontal whitespace is not significant and carries no structure. Indentation
is presentation: steps at the same depth begin at column 10 in one file and 11
in another. Structure comes from the step number. The single exception is the
chain line, noted below.

## Kinds

`db/notation.db` declares the kind of each hole of each notation, and kinds are
what tell two notations sharing a pattern apart. So a parser has to know the
kind of every name before it can read a formula: `|x|` is an absolute value or
a cardinality according to what `x` is.

**Every kind is written on the page, and a parser infers none.** A name's kind
comes from any line in scope that states its membership of a number system, or
from a `define`. In practice that is:

- a `let` line, in the statement or opening a block;
- the claim of the `obtain` step that introduces the name, which states its
  membership as one of its own sentences;
- the right-hand side of a `define`, whose notation says what it yields;
- any numbered step claiming the membership, which need not be the line that
  introduced the name.

The last is what keeps the kinds flat. A `let` line naming a number system
gives a kind directly, but 21 of the corpus's 72 memberships name a set instead:
`s ∈ [a, b]`, `a ∈ S`, `x ∈ A`. The kinds have `set` and no way to say *a set of
numbers*, so those declarations give nothing. The alternative was to let a set
carry the kind of its elements, which turns a flat list of seven words into a
system with parts inside it, and the corpus does not need it.

It does not need it because a bar is settled either by the operator inside it,
as `|s − c|` is by subtraction and `|X ∖ {a}|` by difference, or by a bare
variable whose kind is stated somewhere in scope. Exactly one variable is
declared loosely and later firmed: `s` in the intermediate value proof, declared
`s ∈ S` and given a number kind by step 17.25.3, which precedes the step writing
`|s − c|`. That step exists because the membership rule requires every atom of an
`inequalities` step to be shown real, so the rule that made the corpus more
verbose also made it parseable.

What this leaves open is a bare variable of no known kind sitting directly
inside bars. That is ambiguous, so a parser rejects it rather than choosing, and
the failure is a refused proof rather than a misread one. Today's checker cannot
see it, since it treats a claim as opaque text, and it belongs on the formula
parser's list.

### What flat kinds cost in set theory

set.mm is ZF, so a number *is* a set: 0 is the empty set, 2 is {∅, {∅}}, and ℕ
is the set of finite von Neumann ordinals. The rule above gives a name the kind
`number` as soon as it sees `n ∈ ℕ`, and a number is not a set here. So these
cannot be written:

| statement | why |
|---|---|
| `\|n\| = n` for a natural n | the bars read as absolute value, not cardinality |
| `n ⊆ m` | subset takes two sets and n is a number |
| `x ∈ n` | membership's right hole takes a set |
| `2 = {∅, {∅}}` | the two sides have different kinds |

Most set theory is unaffected, because it does not use the encoding. Cantor's
theorem already works, saying `let A be a set` and never asking what is inside.
Schröder–Bernstein is injections between sets. The countability of ℚ is a
bijection between two things declared as sets, with arithmetic happening where
their elements are numbers. The uncountability of ℝ is numbers throughout. What
is lost is theorems whose content *is* the encoding: cardinal arithmetic,
ordinal arithmetic, and anything unfolding what a number is made of.

That loss is the policy of `READERS.md` enforced one level down. It hides class
variables, set-existence hypotheses and the set-theoretic apparatus from the
reader, and the primes pilot settled that ℕ ⊆ ℤ is an inclusion rather than a
change of type. A reader with school mathematics is not meant to learn that 2 is
a pair of nested empty sets.

If such a theorem is ever wanted the fix is a database addition, not a redesign:
declare ordinals as their own kind, or declare a coercion notation so the text
says where the encoding is being used. That is the honest form regardless, since
a step resting on `2 = {∅, {∅}}` should be visible as one.

The second is the rule that keeps this bounded. Without it a parser would chase
the cited item's conclusion to learn what an obtained name is, and two
implementations chasing to different depths would parse the same formula
differently. All sixteen `obtain` steps in the corpus already state the
membership, so the rule costs nothing and the checker enforces it.

The kinds are `number`, `set`, `point`, `formula`, `function`, `variable`, and
`any`, which means any term kind and never a formula.

## Reading a run of letters

A run of letters is a declared word if one matches by longest match, and
otherwise it is a single variable name. Every variable in the corpus is one
letter with an optional subscript or prime, 26 of them; the declared patterns
contribute 33 literal words.

That rule is only decidable because **juxtaposition never joins two bare
names**. `a·b` is written with the dot, as the corpus writes every product of
named variables, and juxtaposition is left with a numeral before a name, as in
`2k`, and a name before a bracket, as in `k(k + 1)`. Without the restriction
the letters `and` could be a product of `a`, `n` and `d`, all three of which
are variables here, and nothing reading left to right could tell that from the
connective.

## Reading a run of digits

A numeral is a maximal run of digits, so `10` is one token and never a `1`
juxtaposed with a `0`. That matters because a numeral juxtaposed with a name is
how `2k` works, and the two shapes would otherwise compete.

**A decimal point is not written.** A fraction is written as a fraction, `1/2`
rather than `0.5`. The corpus uses four numerals in total, `0`, `1`, `2` and
`4`, none of them multi-digit and none with a point, so this costs nothing
today. set.mm is the precedent: its decimal constructor builds decimal
*integers* and the library has no decimal-point notation at all, writing
fractions with division. Pure mathematics does the same.

The case that looks like a counterexample is not one. Your selection table
notes that Hammack proves ℝ uncountable using decimals, but the diagonal
argument needs a decimal *expansion*, a function from an index to a digit, and
no literal notation would help write it. set.mm's divisibility-by-three rule is
the same shape, stated for digit sequences as sums.

Keeping the point free also keeps it available to end a sentence. Were decimals
ever genuinely needed, the order to try things in is: keep the period for both
and accept that whitespace then matters at a sentence boundary, which would be
its second load-bearing use after the chain line; and only if that hurts, change
the sentence separator, which is ours to choose where the decimal point is not.
The comma is the continental convention but is already a separator here in five
places, and the middle dot is multiplication.

## Where two names run together

Two notations put holes side by side with no token between them: distance
writes `|CA|` and the angle writes `∠PQR`. The names filling them run together
in the text, so they could spell a declared word. Points are capitals
throughout this corpus, which keeps `|AN|` clear of the word `an`, but that is
a convention of school geometry rather than a rule. Topology and differential
geometry both name points with lowercase letters, and set.mm's plane is ℂ,
where a point would naturally be `z` or `w`. The checker therefore rejects a
run-together that spells a declared word instead of relying on the convention.

## Substitution

`SYNTAX.md` requires a claim that is an instance of a formula to be a literal
one. Once a formula is a tree that has a precise reading: substitute the parsed
term at every occurrence of the variable, and compare trees.

Parentheses are therefore not compared. They determine the tree and then play
no further part, so two texts that parse the same are the same instance. This
is what lets the sum formula write `(k + 1)((k + 1) + 1)/2`, since substituting
the characters of `k + 1` into `n(n + 1)/2` would give something that parses
quite differently.

A substitution may not capture. If the term names a variable bound where it
lands, the step is rejected and the text carries a variable condition in words
rather than the variable being renamed in silence. The checker enforces this
without a formula parser, by reading the binders of the target line, and no
substitution in the corpus comes close.

## Files

```
<proof file>  ::= { <theorem> }
<theorem>     ::= `theorem` <name>
                  { <hypothesis> }
                  <conclusion>
                  { <define> | <step> }
<hypothesis>  ::= ( `let` <introduction> | `assume` <formula> ) `(` <label> `)`
<introduction>::= <name> `∈` <term>
                | <name> `be a set`
                | <name> `be a point`
                | <name> `:` <term> `→` <term>
<conclusion>  ::= `then` <formula>
<define>      ::= `define` <name> `:=` <term> `(` <label> `)`
```

Theorems appear in dependency order, so every pointer resolves to something
earlier. A `define` line claims nothing and is cited by its label.

A `let` line carries an **introduction**, not a formula. It names something and
says what it is; it asserts nothing, and the four forms above are all of them.
Two of those, `be a set` and `be a point`, are not notations and never appear
inside a formula. `assume` does take a formula, because it does assert.

Quantifying over an arbitrary set is the formula-position counterpart, and it is
a notation: `for every set X, ...`, declared in `db/notation.db` as a binder
with no domain. Ten lines in the corpus use one of these arbitrary forms, four
`be a set`, three `be a point` and three `for every set`, and until they were
declared none of them matched anything.

## Steps

```
<step>  ::= <number> `.` <claim> <justification> { <requires> } [ <block> ]
<claim> ::= <formula> { <formula> }
```

Several formulas mean their conjunction, and **a period followed by whitespace,
or ending the claim, separates them**. Twenty-nine of the corpus's 280 claims
are more than one formula, and all 96 periods inside a claim are separators.

The claim runs from the step number until the first line whose first token is a
justification head, which is why a claim may not begin with one of those fifteen
tokens. No claim in the corpus does, and a parser rejects one that would.

A step numbered `p.n` belongs to the block of the step numbered `p`.

```
<requires> ::= `requires` <formula> `:` <justification>
```

A requires line carries one citation and does not nest.

## Justifications

A justification is a head and a set of optional slots. The slots are:

| slot | written | 
|---|---|
| instantiation | `<name> := <term>` , comma-separated |
| names | `<name> { , <name> } :` , only after `obtain` |
| target | `in line <number>` \| `in <label>` |
| destination | `into line <number>` \| `into <label>` |
| source | `(line <number>)` \| `(<label>)` |
| from | `from <ref> { , <ref> }` \| `from line <number>` |
| reversal | `right to left` |
| start | `starting at <term>` |

The fifteen heads and the slots each admits:

```
<justification> ::=
    ( `def:` | `thm:` ) <name> [ <instantiation> ] [ `,` <from> ]
  | `obtain` <names> ( `def:` | `thm:` ) <name> [ <instantiation> ] `,` <from>
  | `obtain` <name> `from` `line` <number>
  | `exhibit` `,` <from>
  | `substitute` <formula> <source> [ <destination> ] [ `,` <reversal> ]
  | `instantiate` <instantiation> <target> [ `,` <from> ]
  | `algebra` [ `,` <from> ]
  | `arithmetic`
  | `inequalities` [ `,` <from> ]
  | `join` <ref> { `,` <ref> }
  | `contradiction`
  | `fix`
  | `induction` `on` <name> <start> `,` <from>
  | `cases` `,` <from>
  | `calculation`
```

`join` takes its references directly and never the word `from`.

The target of `instantiate` is a line or a label, never an item. Both slots that
name where a fact comes from, the target and `from`, admit only what is written
on the page. An item's sentences reach a proof by being claimed in a numbered
step that cites the item, and later steps cite that number.

`obtain` has two forms. With an item it names its objects with a colon, as in
`obtain q, r: thm:division-algorithm n := c, d := d, from H3, H4`. Without one
it takes a single name and a line, as in `obtain δ from line 17.4`, carrying
neither a colon nor a comma: there is no item to separate the names from, and
no hypothesis list to introduce.

A justification continues onto the next line when it ends with a comma. That is
the only continuation rule, and it covers hypotheses too: the eleventh
hypothesis of the Bezout lemma spans two lines that way. Of 234 justification
lines, 229 are single lines and every one of the rest follows this rule.

Measured on the corpus: 234 justifications fall into 29 shapes, and three of
those shapes occur once each. Nine of the fifteen heads never vary at all.

## Blocks

`contradiction`, `fix`, `induction`, `cases` and `calculation` are justified by
a block. The block is the sub-steps numbered under the step, together with an
opening line or part markers as the method requires.

```
<block> ::= [ <opener> ] { <part> | <step> }
<opener>::= `suppose` <formula> `(` <label> `)`          -- contradiction
          | { <hypothesis> }                             -- fix
<part>  ::= <part marker> [ <hypothesis> ] { <step> }
<part marker> ::= `base` | `step` | `case`
```

A part marker is a bare word on its own line. Which markers a block may carry,
in which order, and whether a part opens with an assumption, are read from that
method's record in `db/methods.db`, not hard-coded: induction declares `base,
step`, and cases declares a repeating `case` whose parts open with `assume`.

## Calculation chains

```
<chain>      ::= <first line> { <chain line> }
<first line> ::= <term> <rel> <term> <citation>
<chain line> ::= <rel> <term> <citation>
<rel>        ::= `=` | `≤` | `<`
<citation>   ::= <ref> [ `,` `right to left` ]
```

The citation is separated from the term by two or more spaces in all 62 chain
lines. A parser should not rely on that. Read the citation from the right end
of the line instead, since it is a reference optionally followed by the
reversal marker, and treat the whitespace as layout.

The claim's relation is `=` if every line is `=`, `≤` if every line is `=` or
`≤`, and `<` if any line is `<`.

## Scope of a citation

A step numbered `a` may cite a step numbered `b` when `b` is an ancestor of `a`,
or `b` shares `a`'s path up to some position and comes before it there. Written
over the dotted components: `b` is in scope for `a` when `len(b) ≤ len(a)`,
`b[:-1] = a[:len(b)-1]`, and `b[-1] < a[len(b)-1]`. Steps inside a block that
has closed are not visible outside it, so `17.2` cannot cite `17.1.1` but can
cite `17.1`.

A label is in scope inside the block that declares it and nowhere else. A
theorem's hypothesis labels are in scope throughout its proof.

References cannot be found by scanning a line for digits. Claims are full of
numerals that look like step numbers: a square-root instantiation contains a 2
and an exponent contains a 1. A citation is recognised only by its position in
a parsed justification, never by pattern.

## Database records

```
<record> ::= <kind> <name> { <field> }
<kind>   ::= `notation` | `method` | `definition` | `theorem` | `precedence`
<field>  ::= <field name> <value>
```

A record begins at column 0; its fields are indented, one per line, and a field
value continues on further-indented lines. `#` at the start of a line is a
comment. An item's statement is written with the same `let`, `assume` and
`then` lines as a theorem header, so one parser reads both.

Three definitions carry two `then` groups with a `let` between them, because a
recursive definition's base sentence takes no hypothesis and its step sentence
takes one. They are `def:S`, `def:G` and `def:factorial`.

## Not decided here

- **Whether a claim of several formulas can be cited one formula at a time.**
  `SYNTAX.md` lists this among its unsettled items. The grammar treats a step
  as one citable unit.
- **Everything inside a formula.** Notation, precedence, and the three
  different meanings of the vertical bar.
