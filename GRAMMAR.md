# Grammar

`SYNTAX.md` says what a step must contain and why each form was chosen.
`DATABASE.md` says where things are stored. This document says how the stored
text is read: the line kinds, the justification forms, what a formula is, and
the rules a parser applies. It is written from the ten proofs in `proof/` and
the three database files in `db/`, and every rule below holds on all of them.

It has two halves. The **skeleton** is the text around a formula, and its
productions are written out here. A **formula** is not: it is parsed from the
notations declared in `db/notation.records`, and the section on formulas says how
those declarations become a parse rather than listing them again. Adding a
notation is a database entry and never a change to this document.

Every production below is checked against the corpus. All 246 justifications
match a declared production, all 22 labels match their pattern, the only part
markers are the three declared, and no step is numbered under a parent that
does not exist.

Notation used below: `<x>` a named part, `[x]` optional, `{x}` zero or more,
`a | b` alternatives. Literal text is in `code`.

## Lexical rules

Files are UTF-8 in Normalisation Form C. An implementation works in Unicode
scalar values; UTF-16 is used nowhere, for the reason in `DATABASE.md`. Every
non-ASCII character in a claim must appear in `db/notation.records`, which doubles
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
- `<term>` and `<formula>` are given by the notations declared in
  `db/notation.records`, under "Formulas" below. The skeleton rules here delimit
  them; they do not describe what is inside.

Horizontal whitespace is not significant and carries no structure. Indentation
is presentation: steps at the same depth begin at column 10 in one file and 11
in another. Structure comes from the step number. The single exception is the
chain line, noted below.

## Sorts

`db/notation.records` declares the sort of each hole of each notation, and sorts are
what tell two notations sharing a pattern apart. So a parser has to know the
sort of every name before it can read a formula: `|x|` is an absolute value or
a cardinality according to what `x` is.

They are **sorts** in the sense of many-sorted logic, and a set's sort has the
kind of what it holds: *set of numbers*, *set of points*, *set of sets of
numbers*. That is `READERS.md`'s reader, who thinks of a set as holding one kind
of thing. What a name is declared is written down; how the kinds of names
relate is read off the text, as below; and a statement about every set is about
a set of one unknown kind, not a set of anything at all. Above all a sort never
affects meaning. It picks which notation applies, and after that the meaning is
the notation's. Metamath has the same idea one layer down and calls them
typecodes, of which set.mm has three; your goals document's "no types beyond
typecodes" is the kernel drawing this same line, and kinds do not cross it: the
kernel never sees one.

**Every declaration is written on the page, and how kinds relate is read off
it.** A name's sort comes from a line in scope that introduces it or states its
membership, or from a `define`. In practice that is:

- a `let` line, in the statement or opening a block;
- the claim of the `obtain` step that introduces the name, which states its
  membership as one of its own sentences;
- the right-hand side of a `define`, whose notation says what it yields;
- any numbered step claiming the membership, which need not be the line that
  introduced the name.

A `let` line naming a number system gives a sort directly, but 21 of the
corpus's 72 memberships name a set instead: `s ∈ [a, b]`, `a ∈ S`, `x ∈ A`.
Those give the name the kind of what the set holds: `[a, b]` holds numbers, so
`s ∈ [a, b]` makes s a number, and `a ∈ X` makes a whatever kind X holds.

**Kinds are read off how the text uses its names.** Nobody writes "X and Y are
sets of the same kind", and nothing here asks it. Each notation relates the
kinds of its holes — `X ∪ Y` and `X ⊆ Y` join two sets of one kind, `a ∈ X`
makes a the kind X holds, `𝒫X` holds sets of X's kind, `{x}` holds x's kind,
`{t ∈ X : P(t)}` has X's kind, `|X|` is a number whatever X holds — and a name
takes the most general kind the text allows. What the text does not link stays
independent: a bijection may run from a set of numbers to a set of points.
The most general kind is unique, so two parsers reading the same statement
assign the same kinds, which is what `GOALS.md`'s comparable elaborators need.
Nothing is chased into a cited item to find it: a statement is read on its own,
and citing it gives each use its own copy of its kinds.

A few consequences, each a decision of 2026-09-23:

- Two kinds joined where the text needs one is a defect reported where it is
  written, and so is a set that would hold two kinds: `{3, P}`, for a number
  and a point, has no kind.
- `∅` has whichever kind its place gives it, so the empty set of points is not
  compared with the empty set of numbers.
- Inside a proof, "for every set X" ranges over sets of the one kind the proof
  is about. A theorem is general in its kinds when it is cited, so each citing
  step takes the kind it needs; a lemma a proof needs at two kinds is stated as
  its own theorem.
- A name is introduced without claiming a kind by `let a ∉ X`, which gives it
  the kind X holds, or by `let x be an element`, which leaves its kind to the
  text. `let x be a set` claims more, and makes whatever holds x a set of sets.

The bar is settled the same way it always was, by the operator inside it, as
`|s − c|` is by subtraction and `|X ∖ {a}|` by difference, or by the sort of a
bare variable. With kinds, `s` in the intermediate value proof is a number from
its declaration `s ∈ S`, where `S` is a set-builder over `[a, b]`; with flat
sorts it waited for step 17.25.3 to say `s ∈ ℝ`.

**Status.** The parser and checker today implement flat sorts: a set has the
sort `set` and nothing about what it holds, and nothing is inferred. A scratch
checker has inferred kinds over the whole corpus under these rules and found no
clash in 16 proofs and 108 statements, and no statement that narrows another
where it is cited.

**The parser checks every hole against its declared sort**, not only where two
notations compete. The sorts are declared, and an unchecked declaration rots;
with checking, `S ⊆ 2` is a defect a parser reports where nothing in the system
could previously have noticed it. The price is the set-theory restriction below.
A value of no known sort is the exception and fits anywhere, for the reasons
given at the end of this section.

What this leaves open is a bare variable of no known sort sitting directly
inside bars. That is ambiguous, so a parser rejects it rather than choosing, and
the failure is a refused proof rather than a misread one. The checker reports it:
it parses every formula in the corpus, and two of the places it found were a
step whose name came from a `define` and an item that never said its Y was a
set.

**A value of no known sort fits any hole.** Under the flat sorts the parser
implements today, five places in the corpus need this, all of them `s` in the
intermediate value proof, declared `let s ∈ S` where `S` is a set-builder so
the declaration gives no number sort. Four are order comparisons and one is
`f(s) < 0`. Three of the five are the quantified sentences at steps 6, 10 and
17.25, where `s` is bound by the binder and the sort has to come from what `S`
holds. With kinds all five have a sort from their declaration, and the rule is
left for a name whose kind the text genuinely leaves open.

Refusing them would be the sort system rejecting proofs for failing a test it
was never introduced to run: `≤` and `<` are not overloaded, so nothing is
ambiguous in any of the five. So checking is real but partial, and it is worth
being precise about what that costs, because it is less than it sounds.

The failure worth fearing is the parser reading one formula while the reader
reads another, since then the kernel proves something the page does not say.
That cannot happen at any setting of this rule. It needs the parser to choose
wrongly between two notations, and where two compete and the sort is unknown
the formula is ambiguous and the parser refuses. It reads correctly or stops.

What gets past parsing is unambiguous but wrongly sorted text, and elaboration
catches most of it. A step writing `s ≤ b` with `s` not a number still needs
`requires s ∈ ℝ`, because the membership rule makes every atom of an
`inequalities` step a written dull fact, and that requires line cannot be
discharged. The verbosity that rule costs is doing double duty here.

The residue is not unsound and mostly not wrong. If `s ⊆ X` slips through with
`s` a number, that is a meaningful statement in ZF and may be true, since 2
really is a set. What the sorts encode is `READERS.md`'s policy that a number is
presented as a number, which the kernel does not share and has no reason to.

So the stages catch different things: parsing catches ambiguity and any sort
that is known and wrong, elaboration catches the rest through the membership
dull facts, and the kernel guarantees soundness regardless because it works with
classes. Nothing unsound reaches the archive. What is lost is that a proof can
break our own presentation convention and be found out late rather than early.

### What kinds cost in set theory

set.mm is ZF, so a number *is* a set: 0 is the empty set, 2 is {∅, {∅}}, and ℕ
is the set of finite von Neumann ordinals. The rule above gives a name the sort
`number` as soon as it sees `n ∈ ℕ`, and a number is not a set here, nor is
anything a set of numbers holds. Because holes are checked rather than merely
disambiguated, these cannot be written:

| statement | why |
|---|---|
| `\|n\| = n` for a natural n | the bars read as absolute value, not cardinality |
| `n ⊆ m` | subset takes two sets and n is a number |
| `x ∈ n` | membership's right hole takes a set |
| `2 = {∅, {∅}}` | the two sides have different sorts |

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
declare ordinals as their own sort, or declare a coercion notation so the text
says where the encoding is being used. That is the honest form regardless, since
a step resting on `2 = {∅, {∅}}` should be visible as one. A set holding two
kinds at once, which the page refuses, wants the same remedy where it is ever
wanted, a tuple encoded as a set among them.

The second is the rule that keeps this bounded. Without it a parser would chase
the cited item's conclusion to learn what an obtained name is, and two
implementations chasing to different depths would parse the same formula
differently. All sixteen `obtain` steps in the corpus already state the
membership, so the rule costs nothing and the checker enforces it.

The sorts are `number`, `set`, `point`, `formula`, `function`, `variable`, and
`any`, which means any term sort and never a formula.

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

It also keeps step numbers readable, which is the other thing the period does
here. A step number is digits separated by periods, `1.2.3.4`, so it is not a
numeral but a distinct token, and the two could compete: `1.2` is either one
step number or the numeral 1, a sentence boundary, and the numeral 2.

Forbidding the decimal point is what separates them, and it separates them
completely. Inside a claim a period is always a sentence boundary, because it is
always followed by whitespace: no claim in the corpus contains digit-period-
digit, and with no decimals none can. Outside a claim, in a `from` list or a
chain line, digits separated by periods are always a step number. So the two
readings never meet.

A step number's own terminating period needs no rule of its own either. In
`1.2.3.4.  n is even` the number stops at the last digit, since the period after
it is followed by a space rather than a digit, and the step production takes the
period. All 254 steps are written that way, 199 with two spaces after and 55
with one, and the count does not matter because the spacing carries nothing.

Keeping the point free also keeps it available to end a sentence. Were decimals
ever genuinely needed, the order to try things in is: keep the period for both
and accept that whitespace then matters at a sentence boundary, which would be
its second load-bearing use after the chain line; and only if that hurts, change
the sentence separator, which is ours to choose where the decimal point is not.
The comma is the continental convention but is already a separator here in five
places and a connective in a sixth, and the middle dot is multiplication.

## Where two names run together

Two notations put holes side by side with no token between them: distance
writes `|CA|` and the angle writes `∠PQR`. The names filling them run together
in the text, so they could spell a declared word. Points are capitals
throughout this corpus, which keeps `|AN|` clear of the word `an`, but that is
a convention of school geometry rather than a rule. Topology and differential
geometry both name points with lowercase letters, and set.mm's plane is ℂ,
where a point would naturally be `z` or `w`. The checker therefore rejects a
run-together that spells a declared word instead of relying on the convention.

## Formulas

A formula is not parsed from productions written here. It is parsed from the
notations declared in `db/notation.records`, so adding a notation is a database entry
and never a change to this document. What follows is how those declarations
become a parse.

### Tokens

```
<token>   ::= <word> | <name> | <numeral> | <symbol> | `(` | `)`
<word>    ::= a maximal run of letters that is a declared literal, longest match
<name>    ::= a letter, then any subscripts and primes
<numeral> ::= a maximal run of digits
<symbol>  ::= a declared token that is neither letters nor digits
```

A run of letters is a `<word>` if one is declared and a `<name>` otherwise, which
is decidable because juxtaposition never joins two bare names. Round brackets
are the one piece of notation the grammar owns rather than the database: they
group, they take no sort of their own, and `(e)` parses exactly as `e` does.

**A word is at least two letters, and a single letter is always a name.** Three
declared literals are one letter: `a`, from `_, _, _ form a triangle` and
`there is a bijection from _ to _`, and `S` and `G` naming the two sum
functions. All three are also variables in the corpus and `a` is among the
commonest, so longest match without this rule turns every variable `a` into the
article, which it did to 99 sentences before the rule existed.

It costs nothing, because a pattern matches a token by its text and not by the
category the tokeniser filed it under. In `A, B, C form a triangle` the pattern
asks for the text `a` and finds a name spelled `a`; in `S(n)` it asks for `S`
then `(`. What the rule forbids is a notation whose only distinguishing mark is
a lone letter with no bracket or neighbouring word to anchor it, such as a
declared `_ x _`, which is a notation worth forbidding anyway.

At the start of a sentence a declared word also matches with its first letter
capitalised, which is how the corpus writes `For every` and `There is`, 28 times
between them. That allowance is deliberately narrow: matching case anywhere
would let the name `s` match the declared word `S`.

### Applying a notation

```
<term>    ::= <name> | <numeral> | `(` <term> `)` | <applied>
<formula> ::= `(` <formula> `)` | <applied>
<applied> ::= the tokens of some declared pattern, in order, each hole filled by
              a <term> or <formula> whose sort is the hole's declared sort
```

A pattern is a candidate at a position when its leading token matches, a hole
being a token that matches anything. Three things then narrow the candidates, in
this order:

1. **The literal tokens.** Most patterns are settled here alone. Of the 73
   declared patterns two shapes are shared outright, `|_|` and `_(_)`; 21 open
   the same way as some other pattern and are separated by a token further on,
   as `_, _` and `_, and _` are, and as the two universals are by the `with`
   that one of them carries.
2. **The sorts of the holes.** This decides the two overloaded patterns. `|_|`
   is absolute value, cardinality or distance according to what is inside, and
   `_(_)` is a function applied to an argument, a number times a bracketed one,
   or a property holding of something, according to what is on the left.
3. **Nothing else.** Where two candidates survive, the formula is ambiguous and
   the parser reports it rather than choosing. It reads correctly or it stops.

Once a pattern is chosen its holes are checked against their declared sorts, a
value of no known sort fitting any hole.

Continuing an expression is optional, so a pattern that the sorts admit and the
tokens then rule out ends the expression instead of failing the sentence. This
matters because a value of no known sort fits every hole: in `d divides p, and
d divides q` the name `p` is an admissible first point of a triangle, and the
comma after it must be free to end the clause it belongs to.

### Precedence and nesting

A hole is filled by the longest parse that its notation's level permits. Where
two notations meet, the tighter level nests inside the looser, and the order
between levels is the one `precedence order` record. Where two levels are not
related by that record, the expression is ambiguous and needs round brackets.
Two pairs are unrelated on purpose. Conjunction against disjunction is the pair
nobody agrees about, and no formula in the corpus writes it. Negation against a
relation written as words is the pair a reader cannot see: `not n is odd` does
not parse, because it reads as easily as "(not n) is odd", and the brackets in
`not (n is odd)` say which was meant.

A pattern with holes at both edges can nest in itself, and its declared `assoc`
says which way. Fifteen of the 73 patterns are in that position, across ten
records, and the checker enforces that exactly those ten declare one.

### A folded negation

Four notations write a negation inside themselves: `≠`, `∉`, "is not odd" and
"there is no … with …". Each record says so, in a `negates` line naming which of
its patterns is the negation of which, and a parser builds the same tree for the
folded spelling as for the `not`. So `n is not odd` and `not (n is odd)` are one
formula, and the page writes whichever reads better.

Without that line each would be a second spelling of the same thing, which is
the defect the "p is prime" rule was written to prevent. The √2 proof is where
it shows: it offers "n is not odd" to a theorem that assumes "not Q", and no
instantiation of Q reaches a word buried inside a phrase.

The reader still has to be able to see where the negation stops, which is why
the word-phrase relations sit at their own precedence level, unrelated to
negation. `not n is odd` does not parse, because a reader cannot tell it from
"(not n) is odd"; the brackets in `not (n is odd)` are required. A symbolic
relation needs none, since nobody reads `not p = 1` as negating the p.

### What a parser needs besides this

The sort of every name, which comes from the lines described above and is never
inferred. The declared notations, which it reads from the database. And nothing
else: there is no table of operators in this document, and none should be added
here, because a notation is data.

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
                | <name> `∉` <term>
                | <name> `be an element`
                | <name> `be a set`
                | <name> `be a point`
                | <name> `:` <term> `→` <term>
                | <name> `be a property of the elements of` <term>
<conclusion>  ::= `then` <formula>
<define>      ::= `define` <name> `:=` <term> `(` <label> `)`
                  `reads` <words>
```

Theorems appear in dependency order, so every pointer resolves to something
earlier. A `define` line claims nothing and is cited by its label, and the
`reads` line under it says in words what the name means. Both `reads` and the
`note` a block opener may carry are one line each, are the only prose a proof
holds, and are read by no tool: what is checked is that a define has a reading
and that a note belongs to a block. `SYNTAX.md` says why they exist and why
prose is allowed nowhere else.

A `let` line carries an **introduction**, not a formula. It names something and
says what it is; it asserts nothing, and the seven forms above are all of them.
`∉` introduces a thing of the kind a set holds that is not in it, and `be an
element` a thing whose kind the text decides; neither claims the thing is a
set. The last says what a property is a property of, and never names the thing
it holds of, because that name comes from the notation that binds it: in
`{t ∈ X : P(t)}` the braces introduce `t`, and it does not exist above them.
Three of those, `be an element`, `be a set` and `be a point`, are not notations
and never appear inside a formula. `assume` does take a formula, because it
does assert. `thm:add-element-bijection` introduces its `a` by `∉`, and
`thm:card-singleton` and eight other items introduce theirs by `be an
element`. The kernel reads either as the thing being a set as well, since
`{a}` of a proper class is empty; that sethood is apparatus the page never
writes.

Quantifying over an arbitrary set is the formula-position counterpart, and it is
a notation: `for every set X, ...`, declared in `db/notation.records` as a binder
with no domain. Ten lines in the corpus use one of these arbitrary forms, four
`be a set`, three `be a point` and three `for every set`, and until they were
declared none of them matched anything.

## Steps

```
<step>  ::= <number> `.` <claim> <justification> [ <note> ] { <requires> } [ <block> ]
<claim> ::= <formula> { <formula> }
<note>  ::= `note` <words>
```

The note is one line, allowed only where the justification opens a block, and
it says what the block is doing.

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
it takes a line, as in `obtain q, r from line 1`, carrying no colon: there is
no item to separate the names from, and no hypothesis list to introduce.

The second form is preferred, because in the first the name appears in the
claim, which is written above the justification that introduces it. Everywhere
else in this language a name is introduced on its own line before anything
mentions it, by `let` or by `define`. Splitting the step in two restores that:
the first claims that something exists, where the variable is bound by "there
is" and nothing is named, and the second names it and cites that line.

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
method's record in `db/methods.records`, not hard-coded: induction declares `base,
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
