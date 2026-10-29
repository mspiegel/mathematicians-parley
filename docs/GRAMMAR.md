# Grammar

`SYNTAX.md` says what a step must contain and why each form was chosen.
`DATABASE.md` says where things are stored. This document says how the stored
text is read: the line kinds, the justification forms, what a formula is, and
the rules a parser applies. It is written from the proofs in `proofs/`, the
standard library in `corpus/stdlib/` and the notation and methods in `corpus/db/`, and every
rule below holds on all of them. Its examples are kept true as `SYNTAX.md`'s
are: each block's fence says whether it is a `proof`, `records` or `grammar`
block, and `tests/doc_examples.rs` finds every `proof` and `records` block in a
file the build checks.

It has two halves. The **skeleton** is the text around a formula, and its
productions are written out here. A **formula** is not: it is parsed from the
notations declared in `corpus/db/notation.records`, and the section on formulas says how
those declarations become a parse rather than listing them again. Adding a
notation is a database entry and never a change to this document.

### One front end

Text becomes a formula one way (`GOALS.md` decision 18), in three stages,
each done once:

1. The **skeleton reader** cuts a line into its parts by the productions
   below: a step number, a claim, a justification, a label, a requires
   line's fact and its reason, the namings `x := t` of a citation, a `let`
   line's introduction, a chain line's relation, term and citation. A part
   that is formula text is kept as written, with its place in the file.
2. The **splitter** cuts a formula part into sentences at its full stops
   (the lexical rule below), and drops them. Nothing else removes a full
   stop.
3. The **parser** reads each sentence into a tree, by the declared
   notations and the sorts in scope.

A part is one of two kinds. A claim (a step's claim, an `assume` or
`suppose` line, a `then` line) may be several sentences, which mean their
conjunction. Every other part, a `let` line's introduction, a requires
line's fact, a substitute's equation, a value, a chain term or row, an
induction's start, is one formula (`Written::formula`), and two sentences
there are a defect.

The splitter and the parser are in `src/formula/page.rs`, and no other code
reaches the parser. The skeleton reader reads its productions word by word,
never by pattern: `src/corpus/skeleton.rs` cuts a justification into its
head and slots, a requires line's reason, a step's first line, a chain
line's citation and modulus, a label, an import and a range line;
`src/corpus/define.rs` cuts a naming line; and `src/sorts/introduction.rs`
reads which of its forms a `let` line takes. A word is a whole word, so
`into` is never the end of `mun:function-into` and `from` never the middle
of a formula. Everything inside a formula part is read by the parser alone. A check that asks what a claim says asks its tree, never its
text, and a formula a tool makes for itself, such as the membership a `let`
line introduces, is a tree it builds, not a string it parses. A part that
does not read is a defect reported where it is written; a check never passes
over it.

Every production below is checked against the corpus. All 246 justifications
match a declared production, all 22 labels match their pattern, the only part
markers are the three declared, and no step is numbered under a parent that
does not exist.

Notation used below: `<x>` a named part, `[x]` optional, `{x}` zero or more,
`a | b` alternatives. Literal text is in `code`.

## Lexical rules

Files are UTF-8 in Normalisation Form C. An implementation works in Unicode
scalar values; UTF-16 is used nowhere, for the reason in `DATABASE.md`. Every
non-ASCII character in a claim must appear in `corpus/db/notation.records`, which doubles
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
  `nat0-successor`. Every item's name is lowercase words joined by hyphens; the
  capital is there for the name a naming line gives a function, `S` in
  `let S(m) = …`.
- `<module>` is `<name> { / <name> }`, a file's path from the root of the
  corpus without its extension: `stdlib/numbers`, `proofs/wiedijk/bezout`.
- `<cited>` is a `<name>`, what follows an item's prefix, `thm:` or another:
  the name the file imports the item under, or a theorem of the citing file.
  "Names" below says how one is resolved.
- `<term>` and `<formula>` are given by the notations declared in
  `corpus/db/notation.records`, under "Formulas" below. The skeleton rules here delimit
  them; they do not describe what is inside.

Horizontal whitespace is not significant and carries no structure. Indentation
is presentation: steps at the same depth begin at column 10 in one file and 11
in another. Structure comes from the step number. The single exception is the
chain line, noted below.

## Sorts

`corpus/db/notation.records` declares, in each notation's `sort` field, the sort of each
hole and of what the notation produces, and sorts are what tell two notations
sharing a pattern apart. So a parser has to know the sort of every name before
it can read a formula: `|x|` is an absolute value or a cardinality according to
what `x` is.

They are **sorts** in the sense of many-sorted logic, and they nest: a set's
sort says what it holds, so *number*, *set of numbers*, *set of points* and *set
of sets of numbers* are four sorts. A pair's sort is the sorts of its two
parts, *pair of a number and a point*, and `A × B` holds the pairs of what A
and B hold. That is `READERS.md`'s reader, who thinks of
a set as holding one sort of thing. What a name is declared is written down; how
the sorts of names relate is read off the text, as below; and a statement about
every set is about a set of one unknown sort, not a set of anything at all.
Above all a sort never affects meaning. It picks which notation applies, and
after that the meaning is the notation's. Metamath has the same idea one layer
down and calls them typecodes, of which set.mm has three; your goals document's
"no types beyond typecodes" is the kernel drawing this same line, and sorts do
not cross it: the kernel never sees one.

**Every declaration is written on the page, and how sorts relate is read off
it.** What a line states and what its formulas imply are facts of one reading,
made in the order the lines are written, each line parsed with what the lines
above it settled. A name's sort comes from a line in scope that introduces it or
states its membership, from a `define`, or from how a formula uses it. The
declarations are:

- a `let` line, in the statement or opening a block;
- the claim of the `obtain` step that introduces the name, which states its
  membership as one of its own sentences;
- the right-hand side of a `define`, whose notation says what it yields;
- any numbered step claiming the membership, which need not be the line that
  introduced the name.

A membership gives the name the sort of what the set holds, whether the set is
a number system or not: `n ∈ ℕ` makes n a number because ℕ is a set of numbers,
`s ∈ [a, b]` makes s a number because `[a, b]` holds numbers, and `a ∈ X` makes
a whatever sort X holds.

**Sorts are read off how the text uses its names.** Nobody writes "X and Y are
sets of the same sort", and nothing here asks it. Each notation relates the
sorts of its holes — `X ∪ Y` and `X ⊆ Y` join two sets of one sort, `a ∈ X`
makes a the sort X holds, `𝒫X` holds sets of X's sort, `{x}` holds x's sort,
`{t ∈ X : P(t)}` has X's sort, `|X|` is a number whatever X holds, `k + 1`
makes k a number — and a name takes the most general sort the text allows.
What the text does not link stays independent: a bijection may run from a set
of numbers to a set of points. The most general sort is unique, so two parsers
reading the same statement assign the same sorts, which is what `GOALS.md`'s
comparable elaborators need. Nothing is chased into a cited item to find it: a
statement is read on its own, and citing it gives each use its own copy of its
sorts.

A few consequences, each a decision of 2026-09-23:

- Two sorts joined where the text needs one is a defect reported where it is
  written, and so is a set that would hold two sorts: `{3, P}`, for a number
  and a point, has no sort.
- `∅` has whichever sort its place gives it, so the empty set of points is not
  compared with the empty set of numbers.
- Inside a proof, "for all sets X" ranges over sets of the one sort the proof
  is about. A theorem is general in its sorts when it is cited, so each citing
  step takes the sort it needs; a lemma a proof needs at two sorts is stated as
  its own theorem.
- A name is introduced without claiming a sort by `let a ∉ X`, which gives it
  the sort X holds, or by `let x be an element`, which leaves its sort to the
  text. `let x be a set` claims more, and makes whatever holds x a set of sets.

The bar is settled by the operator inside it, as `|s − c|` is by subtraction
and `|X ∖ {a}|` by difference, or by the sort of a bare variable: `s` in the
intermediate value proof is a number from its declaration `s ∈ S`, where `S` is
a set-builder over `[a, b]`.

**How the tools do it.** `src/sorts/infer.rs` reads a statement or a proof in
the order it is written, parsing each line with the sorts the lines above it
settled and unifying as it goes; a name's sort is what that reading settles. A
name declared of any sort — `be a set`, `be an element` — stays free while its
statement or its block's opening lines may still relate it, and is fixed where
the proof under them begins; from there nothing may narrow it. The checker
reports each clash where it is written, including a citation whose statement
would narrow a set declared of any sort, and each cited statement is read on its
own and copied fresh at each use. A citation checks what a proof's names are and
never says it: a name whose sort only fitting a citation settles is reported,
`only the citation says c is a number; say so where c is introduced`, so a
proof's sorts come from its own lines, as the elaborator reads them.

The parser tells two readings apart by a coarser class than the sort, its
**category**: a number, a point, a statement, a group element, a set, a set of
group elements, a set of sets, a function, a property. Each notation's holes
and result take the category of the sort its `sort` field gives them, and a
hole its `binds` line says introduces a name takes a name. Where a formula still
reads two ways, the checker names the readings and the names nothing gives a
sort: `'|W| = 2^k' reads as absolute-value or as cardinality, and nothing says
what W is`.

**The parser checks every hole against its category**, not only where two
notations compete. The sorts are declared, and an unchecked declaration rots;
with checking, `S ⊆ 2` is a defect a parser reports, and `s exists` with s a
number is reported as `s is a number, and `_ exists` wants a set`. The price
is the set-theory restriction below. A value of no known sort is the exception
and fits anywhere, for the reasons given at the end of this section.

What this leaves open is a bare variable of no known sort sitting directly
inside bars. That is ambiguous, so a parser rejects it rather than choosing, and
the failure is a refused proof rather than a misread one. The checker reports it:
it parses every formula in the corpus, and two of the places it found were a
step whose name came from a `define` and an item that never said its Y was a
set.

**A value of no known sort fits any hole.** Most such values are names a
quantifier binds: `for all s ∈ S, d ≤ s`, `there are m ∈ ℤ and n ∈ ℤ with
d = a·m + b·n`. What such a name is, is what its domain holds. A theorem's sorts
are a name's for the whole theorem, and a bound name is not one, since the same
letter may be bound over a set of numbers in one sentence and a set of sets in
another; so a letter written `x ∈ S` takes, for that sentence, the sort of what
S holds where S's sort says, and is otherwise of no known sort, and this rule is
what lets it through. A set whose members' sort is still open fits a hole that
wants a set of sets: `let G be a set` says nothing of what G holds, and a
phrase whose slot holds sets, as E does in `W is a clique in E of size at
least n`, settles it.

Refusing such values would be the sort system rejecting proofs for failing a
test it was never introduced to run: where one sits where two notations
compete, the formula reads two ways and is refused anyway. So checking is real
but partial, and it is worth being precise about what that costs, because it is
less than it sounds.

The failure worth fearing is the parser reading one formula while the reader
reads another, since then the kernel proves something the page does not say.
That cannot happen at any setting of this rule. It needs the parser to choose
wrongly between two notations, and where two compete and the sort is unknown
the formula is ambiguous and the parser refuses. It reads correctly or stops.

What gets past parsing is unambiguous but wrongly sorted text, and elaboration
catches most of it. A step writing `s ≤ b` with `s` not a number needs s to be
real, because every atom of an `inequalities` step must be: no line
introduces s into a number system, so the page does not say it once, and a
`requires s ∈ ℝ` line cannot be discharged either.

The residue is not unsound and mostly not wrong. If `s ⊆ X` slips through with
`s` a number, that is a meaningful statement in ZF and may be true, since 2
really is a set. What the sorts encode is `READERS.md`'s policy that a number is
presented as a number, which the kernel does not share and has no reason to.

So the stages catch different things: parsing catches ambiguity and any sort
that is known and wrong, elaboration catches the rest through the membership
every number needs, and the kernel guarantees soundness regardless because it works with
classes. Nothing unsound reaches the archive. What is lost is that a proof can
break our own presentation convention and be found out late rather than early.

### What sorts cost in set theory

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
sorts at once, which the page refuses, wants the same remedy where it is ever
wanted, a tuple encoded as a set among them.

An `obtain` step states the membership of what it obtains, and that rule keeps
this bounded. Without it a parser would chase the cited item's conclusion to
learn what an obtained name is, and two implementations chasing to different
depths would parse the same formula differently. Every `obtain` step in the
corpus states the membership, so the rule costs nothing, and the checker
enforces it.

The categories are `number`, `set`, `point`, `formula`, `function`, `property`,
`group-element`, `group-set` and `set-of-sets`; a hole may also take `variable`,
a name its notation binds, or `any`, any term and never a formula, for a hole
whose sort is a variable. The three categories of a set fit where a set is
wanted, and a set's sort says what its members are: `for all g ∈ G, g ∈ gH`
reads g as the group's element, and `for all Y ∈ K, |Y| = m` reads |Y| as a
size where K's members are sets.

A hole whose category is `group-element` takes nothing of unknown sort: `k·m`
with neither sort known is a product of numbers, and a letter is a group's
element only where the page says so or says what it ranges over.

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

The one exception is the coset `gH`, which a school reader writes that way and
no other. Two bare names are joined there only where the first is a group's
element and the second a set of them, which the sorts decide before any
letter is read as a word: `a`, `n` and `d` are never a group's element and a
set of them at once.

## Reading a run of digits

A numeral is a maximal run of digits, so `10` is one token and never a `1`
juxtaposed with a `0`. That matters because a numeral juxtaposed with a name is
how `2k` works, and the two shapes would otherwise compete.

**A decimal point is not written.** A fraction is written as a fraction, `1/2`
rather than `0.5`. The corpus writes digits and one numeral of two, `10`, and
none with a point, so this costs nothing today. set.mm is the precedent: its
decimal constructor builds decimal *integers*, which is how `10` reaches the
kernel, as `; 1 0`, and the library has no decimal-point notation at all,
writing fractions with division. Pure mathematics does the same.

The case that looks like a counterexample is not one. Your selection table
notes that Hammack proves ℝ uncountable using decimals, but the diagonal
argument needs a decimal *expansion*, a function from an index to a digit, and
no literal notation would help write it. The divisibility-by-three rule is the
same shape, and the pilot states it so: a digit function d, and the number as
`Σ(k = 0 to n) d(k)·10^k`.

It also keeps step numbers readable, which is the other thing the period does
here. A step number is digits separated by periods, `1.2.3.4`, so it is not a
numeral but a distinct token, and the two could compete: `1.2` is either one
step number or the numeral 1, a sentence boundary, and the numeral 2.

Forbidding the decimal point is what separates them, and it separates them
completely. Inside a claim a period is always a sentence boundary, because it is
always followed by whitespace: no claim in the corpus contains digit-period-
digit, and with no decimals none can. Outside a claim, in a `from` list or a
chain line, digits separated by periods are always a step number. So the two
readings never meet. A claim may end on a full stop or not, and means the same
either way: the splitter drops every full stop it cuts at, the last included,
and is the only stage that sees one.

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
notations declared in `corpus/db/notation.records`, so adding a notation is a database entry
and never a change to this document. What follows is how those declarations
become a parse.

### Tokens

```grammar
<token>   ::= <word> | <name> | <numeral> | <raised> | <symbol> | `(` | `)`
<word>    ::= a maximal run of letters that is a declared literal, longest match
<name>    ::= a letter, then any subscripts and primes
<numeral> ::= a maximal run of digits
<raised>  ::= a maximal run of the raised digits ⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹
<symbol>  ::= a declared token that is neither letters nor digits
```

A `<raised>` token is a numeral written raised, and stands where a notation's
pattern writes `ⁿ`: the superscript record's `_ⁿ` reads x², N³ and 2¹⁰ as
powers whose exponent is the numeral 2, 3 or 10. One record serves every such
exponent, as one `<numeral>` serves every number. An exponent with a letter in
it is written with `^`, as in 2^n: raised letters are not a complete alphabet,
and a power would then have two spellings. A raised numeral before √ is a
root's index (Powers and roots).

A run of letters is a `<word>` if one is declared and a `<name>` otherwise, which
is decidable because juxtaposition never joins two bare names. Round brackets
are the one piece of notation the grammar owns rather than the database: they
group, they take no sort of their own, and `(e)` parses exactly as `e` does.

A function applied is of the sort its function maps to: `cos(x)` is a number,
so `|cos(x)|` is an absolute value and not the size of a set. Where a
notation's record leaves what it yields to a sort variable, as application's
`function from α to β, α → β` does, the sorts of what fills its holes settle
it.

A notation may still open with a bracket, as the pair `(a, b)` does. It is
tried as a notation opening with a name is, and what no such notation reads is
a group: the pair's comma between two holes is what tells it from `(e)`.

A prime always belongs to a name to the lexer, and what a primed name means is
the parser's to say, by the sort of its stem. Where nothing declares `f′` and
f is a function, `f′` is the derivative of f, written `_′` in the notation
records, and `f′′` the derivative of `f′`; `f′(x)` is that function applied to
x. Where the stem is a point or a number, or nothing at all, c′ and P′ are names
like any other. Declaring `f′` beside a function f is a defect, since a reader
takes it for the derivative: the checker says to call it f₁.

Where f is a function, `f^(n)` is its n-th derivative, the exponent in
parentheses: `f^(0)` is f, `f^(1)` is `f′`, and `f^(k + 1)` is the derivative of
`f^(k)`. The stem's sort decides, as for `f′`: where f is a number, `f^(n)` is a
power. A function to a power without the parentheses, `f^n`, is refused.

`deg(_)` is read by its argument's sort in the same way: of a vertex, it is
the vertex's degree in its graph; of a function from numbers to numbers, a
polynomial's degree.

**A word is at least two letters, and a single letter is always a name.** One
declared literal is one letter: `a`, from `_, _, _ form a triangle` and
`there is a bijection from _ to _`. It is also among the commonest variables in
the corpus, so longest match without this rule turns every variable `a` into the
article, which it did to 99 sentences before the rule existed.

It costs nothing, because a pattern matches a token by its text and not by the
category the tokeniser filed it under. In `A, B, C form a triangle` the pattern
asks for the text `a` and finds a name spelled `a`. The binomial coefficient's
`C(n, k)` is no literal at all: it is the library function C applied to n and k
("Database records"). What the rule forbids is a notation whose only distinguishing mark is
a lone letter with no bracket or neighbouring word to anchor it, such as a
declared `_ x _`, which is a notation worth forbidding anyway.

At the start of a sentence a declared word also matches with its first letter
capitalised, which is how the corpus writes `For all`, `There is` and `There
exists`, 85 times between them. That allowance is deliberately narrow: matching case anywhere
would let the name `s` match the declared word `S`.

### Applying a notation

```grammar
<term>    ::= <name> | <numeral> | `(` <term> `)` | <applied>
<formula> ::= `(` <formula> `)` | <applied>
<applied> ::= the tokens of some declared pattern, in order, each hole filled by
              a <term> or <formula> whose sort is the hole's declared sort
```

A pattern is a candidate at a position when its leading token matches, a hole
being a token that matches anything. Four things then narrow the candidates, in
this order:

1. **The literal tokens.** Most patterns are settled here alone. Of the 80
   declared patterns three shapes are shared outright, `|_|`, `_(_)` and
   `(_, _)`; others
   open the same way as some other pattern and are separated by a token further
   on, as `_, _` and `_, and _` are, as the two universals are by the `with`
   that one of them carries, and as `{_}` and `{_, …, _}` are by the comma.
2. **The sorts of the holes.** This decides the two overloaded patterns. `|_|`
   is absolute value, cardinality or distance according to what is inside, and
   `_(_)` is a function applied to an argument, a number times a bracketed one,
   or a property holding of something, according to what is on the left.
3. **The place it fills.** This decides `(_, _)`, whose holes cannot tell its
   readings apart. A pair of numbers names
   - where the hole it fills wants a set, the open interval between its ends;
   - where it wants a point, the point with those coordinates;
   - anywhere else, the pair.

   A hole that takes any term wants what the notation's other parts make it:
   in `A = (1, 2)`, with A a point, the pair is a point. A hole admits one of
   these at most, so this chooses nothing the sorts leave open.
4. **Nothing else.** Where two candidates survive, the formula is ambiguous and
   the parser reports it rather than choosing. It reads correctly or it stops.

Once a pattern is chosen its holes are checked against their declared sorts, a
value of no known sort fitting any hole.

Continuing an expression is optional, so a pattern that the sorts admit and the
tokens then rule out ends the expression instead of failing the sentence. This
matters because a value of no known sort fits every hole: in `d divides p, and
d divides q` the name `p` is an admissible first point of a triangle, and the
comma after it must be free to end the clause it belongs to.

A sentence that does not read is told why where a reading got furthest.
That the text ended before a pattern's next token is the weakest reason,
said only where no reading gave another at the same place: `_ = _ = _` runs
out at the end of `for all η > 0, η = η`, where the binder's own reason is
the one worth saying.

A hole between literals ends where the literals after it follow, all of them
and not only the first. The middle hole of `_ ≡ _ (mod _)` ends at `( mod`,
so the bracket of f(x) in `a ≡ f(x) (mod n)` is f's and not the start of
`(mod n)`.

### Precedence and nesting

A hole is filled by the longest parse that its notation's level permits. Where
two notations meet, the tighter level nests inside the looser, and the order
between levels is the one `precedence order` record. Where two levels are not
related by that record, the expression is ambiguous and needs round brackets,
whichever side each stands on: an operator extends what stands to its left
only where that binds tighter, as it takes into its right hole only what
binds tighter, and a bracketed group is closed and extends at any level.
Three pairs are unrelated on purpose. Conjunction against disjunction is the
pair nobody agrees about, and no formula in the corpus writes it. Negation
against a relation written as words is the pair a reader cannot see: `not n
is odd` does not parse, because it reads as easily as "(not n) is odd", and
the brackets in `not (n is odd)` say which was meant. And a universal written
after what it says, `trailing`, against the connectives: in "P and Q for all
x ∈ A" a reader cannot tell whether the "for all" covers P, so the text
brackets what it covers. A relation, a word predicate and a negation bind
tighter than it, so "f(x) ≠ B for all x ∈ A" needs none.
Betweenness stands apart from the connectives the same way. "P is between A
and B" writes an "and" of its own, so in `P = A or P is between A and B or B
is between A and P` a reader has to work out which "and" joins what. It is
written `P = A or (P is between A and B) or (B is between A and P)`. Against
everything else it binds as a word predicate does. A phrase a define gives
whose own words write "and" or "or" stands at betweenness's level, and is
bracketed the same way.

A sum, `Σ(k = 0 to n) t`, holds its summand at its right edge, and its level,
`summation`, sits between multiplication and addition: multiplication binds
tighter, so `Σ(k = 0 to n) d(k)·10^k` sums the product, and addition looser,
so `Σ(k = 0 to n) d(k)·10^k − Σ(k = 0 to n) d(k)` is one sum less another.
A sum of a sum or a difference writes its brackets, `Σ(k = 0 to n) (t(k) −
u(k))`, as a reader expects. A product, `∏(k = 1 to n) t`, is read the
same way at the same level: `∏(k = 1 to n) 2·k` multiplies the doubles, and
`∏(k = 1 to n) (k + 1)` writes its brackets. It is a binder, like `for
all`: the `k` it names is bound in the summand. A congruence, `a ≡ b (mod n)`, is a relation,
and its brackets are part of its pattern, not a grouping.

A sum or a product over a set, `Σ(x ∈ X) t`, may run over a set of anything,
as long as its summand is a number. For example, `Σ(s ∈ 𝒫D) |s|` adds the
sizes of the subsets of D.

`⋂(i ∈ I) A(i)` is the intersection of the sets A(i), one for each i in I:
what is in every one of them. For example, `⋂(X ∈ D) X` is the intersection
of the sets in D.

When I is empty there are no sets to intersect, and the intersection is not a
set. A fact about an intersection therefore assumes `I ≠ ∅`.

A map may be written short, `x ∈ A ↦ e`, as a textbook writes x ↦ e with its
domain. It is `the map sending x ∈ A to e` in another spelling: one notation,
read and built the same way. It binds more loosely than anything else, so
wherever it stands inside other notation it is written in brackets, `(x ∈ [a,
b] ↦ F(x)) is continuous on [a, b]`. Those brackets are grouping, as around
any term. Within it, `x ∈ A` before the arrow is the map's letter and domain,
not a membership: the arrow decides, and a reading that reaches it is taken
over one that stops at `x ∈ A`.

The range a sum runs over is written as a set, `{0, …, n}`, where a line says
something of every index in it: "for all k ∈ {0, …, m}, …" is the line a
sum over 0 to m is rewritten term by term from. `C(n, k)`, n choose k, is the
library function C applied to n and k, and a theorem that calls a point or a
set C means its own C, since the library's sort for a name applies only where
the theorem introduces no name of that letter.

A pattern with holes at both edges that yields what those holes take can nest
in itself, and its declared `assoc` says which way: `left` chains from the
left, as `a − b − c` is (a − b) − c, and `right` nests in its own last hole,
as `a^2^3` is a^(2^3). Twenty of the 100 patterns are in that position, across
fifteen records, and the checker enforces that exactly those fifteen declare
one.

### A folded negation

Four notations write a negation inside themselves: `≠`, `∉`, "is not odd" and
"is not incident with". Each record says so in a `negates` line, which names
which of its patterns is the negation of which. A parser builds the same tree
for the folded spelling as for the `not`. So `n is not odd` and `not (n is odd)`
are one formula, and the page writes whichever reads better.

Every "there is" and "there exists" folds a negation by one rule, so its record
needs no `negates` line. "There is" and "there are" take "no" after them, and an
"a" right after them gives way to the "no". "There exists" becomes "there does
not exist", and "there exist" becomes "there do not exist". Each means the
pattern negated. Examples:

- `there is no S ⊆ A with P` is `not (there is S ⊆ A with P)`
- `there is no bijection from A to B` is `not (there is a bijection from A to B)`
- `there are no k, m ∈ ℕ with P` is `not (there are k, m ∈ ℕ with P)`
- `there does not exist δ > 0 such that P` is `not (there exists δ > 0 such that P)`
- `there do not exist x, y ∈ ℤ such that P` is `not (there exist x, y ∈ ℤ such that P)`

Without that line each would be a second spelling of the same thing, which is
the defect the "p is prime" rule was written to prevent. The √2 proof is where
it shows: it offers "n is not odd" to a theorem that assumes "not Q", and no
instantiation of Q reaches a word buried inside a phrase.

The reader still has to be able to see where the negation stops, which is why
the word-phrase relations sit at their own precedence level, unrelated to
negation. `not n is odd` does not parse, because a reader cannot tell it from
"(not n) is odd"; the brackets in `not (n is odd)` are required. A symbolic
relation needs none, since nobody reads `not p = 1` as negating the p.

### A chain of equations

`a = b = c = d` is one notation, `equal-chain`, whose pattern `_ = _ = _`
repeats its last hole after each `=`, as a listed set repeats after each
comma. It opens as `_ = _` does, and the parser takes the reading that goes
further, so `a = b` alone is an equation and `a = b = c` a chain. What it
stands for is the equations between neighbouring terms, joined from the
left: the record's `repeats` line builds each further one with `_′`, the
term before it. A chain is a whole sentence (`SYNTAX.md`); one inside
another formula reads, and the checker reports it.

### Powers and roots

`x^y` is the power a reader means, and its exponent decides which. A whole
exponent makes it a product of copies, set.mm's `↑`: `2^n`, `x^(k + 1)`,
`5^φ(n)`. Any other makes it the principal power e^(y·ln x), set.mm's `↑𝑐`:
`x^(1/3)`, or `2^y` for y ∈ ℝ. For x > 0 this is the real power every reader
means: `x^(1/2)` is √x and `e^y` is exp(y). For x < 0 it is complex, so a fact
about a real power states x ≥ 0 or x > 0, and the real cube root of a negative
number is written `∛x`. An exponent is whole unless it shows otherwise: it
holds a division, π, e, i or a root, a letter the lines above put in ℚ, ℝ or ℂ
or in a set within one, or a function whose values they say are such numbers
(ln, exp, sin, cos, or `f : X → ℝ`). A binder says the same of the letter it
binds, so `for all y ∈ ℝ, 2^y > 0` is a real power. A letter inside a
function's argument does not count, so `5^s(x)` with x ∈ ℚ is whole. The
reading is settled when the line is read, as a sort is, and a later line
proving the exponent whole does not change it.

A root is written with its index raised before √, as `⁵√x`, and `∛x` and `∜x`
are `³√x` and `⁴√x` written as one character. The index is a numeral of 3 or
more, √ alone being the square root. A raised numeral before √ is always an
index, so `2·⁵√x` writes its dot. For an odd index the root is the real root of
every real number, `∛(−8) = −2`; for an even one a fact about it states x ≥ 0.
A root whose index is a letter is written `x^(1/n)`, for x ≥ 0.

### What a parser needs besides this

The sort of every name, which comes from the lines described above and is never
inferred. The declared notations, which it reads from the database. And nothing
else: there is no table of operators in this document, and none should be added
here, because a notation is data. What it is handed is one sentence, as the
splitter cut it (the front end above), never a line or a claim of several.

## Substitution

`SYNTAX.md` requires a claim that is an instance of a formula to be a literal
one. Once a formula is a tree that has a precise reading: substitute the parsed
term at every occurrence of the variable, and compare trees.

Parentheses are therefore not compared. They determine the tree and then play
no further part, so two texts that parse the same are the same instance. This
is what lets the sum formula write `(k + 1)((k + 1) + 1)/2`, since substituting
the characters of `k + 1` into `n(n + 1)/2` would give something that parses
quite differently.

Nor is an identity element compared, here or wherever two trees are. They are
compared as if each operation with its identity in a hole its notation record
allows it (`identity`) were the other hole: n − k at k := 0 is n, and P(n)
saying L(p + n) has L(p) at 0. The element has to be written in one of the
two; a tree is never read as x + 0 to match an x.

A substitution may not capture. If the term names a variable bound where it
lands, the step is rejected and the text carries a variable condition in words
rather than the variable being renamed in silence. The checker enforces this
without a formula parser, by reading the binders of the target line, and no
substitution in the corpus comes close.

## Files

```grammar
<proof file>  ::= { <import> } { <theorem> | <define> }
<import>      ::= `import` ( `mundane` `theorem` | <kind> ) <module> `/` <name>
                  [ `as` <name> ] [ `(` <label> `)` ]
<kind>        ::= `axiom` | `theorem` | `definition`
<theorem>     ::= `theorem` <name>
                  { <theorem field> }
                  { <hypothesis> | <naming> }
                  <conclusion>
                  { <naming> | <step> }
<theorem field> ::= ( `metamath` | `note` ) <words>
<hypothesis>  ::= ( `let` <introduction> | `assume` <formula> ) `(` <label> `)`
<introduction>::= <name> `∈` <term>
                | <name> `∉` <term>
                | <name> `⊆` <term>
                | <name> `be an element`
                | <name> `be a set`
                | <name> `be a point`
                | <name> `be a function on` <term>
                | <name> `:` <term> `→` <term>
                | <name> `:` <term> `→` <term> `be` <property>
                | <name> `be a` [ `finite` ] `group with operation` `·`
                  `and identity` <name>
                | <name> `be a property of the elements of` <term>
                  (a library item's only: `SYNTAX.md`)
<conclusion>  ::= `then` <formula>
<define>      ::= `define` <name> [ `(` <name> `)` ] `:=` <rule>
                  [ `,` `for` <name> ( `∈` | `⊆` ) <term> ] `(` <label> `)`
                  `reads` <words>
                | `define` <name> `:` <phrase> `means` <formula>
                  [ `,` `where` <slot kind> { `,` <slot kind> } ]
                  `(` <label> `)` `reads` <words>
<slot kind>   ::= <slot> `is a set`
                | <slot> `is a function from` <things> `to` <things>
<things>      ::= `numbers` | `points`
<phrase>      ::= <slot> `is` <article> <first> { <piece> }
<first>       ::= <word> | <attached slot>
<piece>       ::= <word> | <slot> | <attached slot>
<attached slot> ::= <name> `-` <word>
<slot>        ::= <name>
<article>     ::= `a` | `an`
<naming>      ::= `let` <name> [ `(` <name> `)` ] `=` <rule>
                  [ `,` `for` <name> ( `∈` | `⊆` ) <term> ] `(` <label> `)`
                  `reads` <words>
                | `let` <name> `=` <term> `,` <kind> `(` <label> `)`
                  <newline> <reason>
                  { <newline> <requires> }
                  `reads` <words>
                | `let` <recursion> `,` `for` <name> `∈` `ℕ₀`
                  `(` <label> `)` `reads` <words>
<recursion>   ::= <name> `(` `0` `)` `=` <rule>
                  { `,` <name> `(` ( `0` | <name> `+` `1` ) `)` `=` <rule> }
<rule>        ::= <term>
                | { <term> `if` <formula> <newline> } <term> `otherwise`
<kind>        ::= one wording in the number systems' `member` field:
                  `a natural number`, `a positive integer`,
                  `a natural number or 0`, `a nonnegative integer`,
                  `an integer`, `a rational number`, `a real number`,
                  `a complex number`
<reason>      ::= what follows the colon of a <requires> line: a
                  justification, `from` and its lines, or
                  <manipulation> `,` `from` <ref>
```

A `<manipulation>` is one of the rows' reasons (Inequality rows) but
`algebra`: a requires line naming one takes its one line to its fact with
that manipulation, as a row is the row above with it. `algebra, from L` is
the method, which rewrites an equation's or a disequality's sides itself.

A `define` is the file's and stands outside every theorem; a `<naming>` is a
`let` followed by `=`, one theorem's, and stands inside it (`SYNTAX.md`). The
two are one line in what follows, and this document calls either a define. A
`define` inside a theorem, and a naming `let` outside one, are defects. What
follows the name tells a naming `let` from a `<hypothesis>`'s: `=`, and not
`∈`, `∉`, `⊆`, `:` or `be`.

A naming `let` that ends with a `<kind>` says its name is that kind of
number, and the `<reason>` on the next line shows the term is: it is read as
a requires line saying `<term> ∈ S` of the first step below the let, and it
cites nothing below the let. Its requires lines give what the reason's item
asks for: they are read as requires lines of the same step, above the
reason's, so the reason rests on them as a requires line rests on those above
it. They cite nothing below the let either. Citing the let's label then gives
the membership beside the equation. A naming `let` in a theorem's statement, before `then`,
says no kind.

A define whose first rule is said at 0 defines sequences by recursion. Each
name it gives has exactly one rule at `0` and one at the index `+ 1`, where
the index is the name after `for`; a rule at any other place, a second rule
at one, or a name missing either is a defect (`parse.recursion_parts`). A
define written between a theorem's hypotheses and its conclusion is part of
the statement, and the conclusion may use the names it gives.

A define continues until the line carrying its label. Written over several
lines whose last ends `otherwise`, it is a function by cases, one case to a
line, and the lines are the term `_ if _, _ otherwise` (`corpus/db/notation.records`,
`by-cases`) nested from the right; set.mm's `if ( P , a , b )` is what it
reads into. Otherwise the lines are one term wrapped.

A define with a name in brackets after its own is a function: `let S(m) =
Σ(j = 1 to m) j, for m ∈ ℕ` says S is the function on ℕ that sends each m to
that sum, as a reader writes "let S(m) = 1 + 2 + … + m". Its domain is said
with it, after `for`, and names the same letter as the brackets; a parameter
with no domain, or a domain with no parameter, is a defect. After it `S(n)` is
S applied to n. Two names in the brackets make a function of two arguments,
`define G(a, n) := …, for a ∈ ℝ, n ∈ ℕ₀`: the `for` clause gives each one's
domain in the brackets' order, split at commas outside brackets so that `x ∈
[a, b]` is one piece, and `G(a, n)` is `application-to-two`. The checker reads it as the rule with n for m wherever it
compares two formulas, and a line whose sides agree read that way cites the
define's label.

What a define names is one letter, perhaps with a subscript or a prime, as
every name in a formula is: the tokeniser reads `avg(x)` as three names, so a
define called `avg` could never be written after it, and it is refused at its
line. The same holds for the name an import of a define gives it, its own or
the one after `as`.

A define of a phrase names no letter: its name is an item's, `<name>` as a
theorem's is, and what it gives is a pattern. The phrase is read word by
word: after `is` the article is a word whatever its length, a `<name>` is a
slot, a `<name>` joined by a hyphen to the word after it an attached slot,
and anything longer a word. Two slots never stand side by side, and a phrase
has one, two or three; a function's two arguments and a phrase's three are
each a form of their own, as `f(x)` and `f(x, y)` are, and no rule speaks of
a phrase of any number. The phrase and its negation, with `not` after `is`,
are added to the grammar of the file that writes the define and of each file
that imports it, and to no other; a phrase another notation already writes
is a defect where it is declared, and is added to no grammar. Each slot takes
the sort its meaning gives the letter. A `where` part gives a slot its sort
before the meaning is read, a set of things of a sort left open or a function
between the sorts it names, and adds nothing to what the phrase says. The
phrase stands at the level
`predicate`, or at `betweenness` where its words write "and" or "or".

Theorems may appear in any order. No theorem cites itself, and no theorems
of a file cite one another round a cycle. A theorem field says what a record's field of the same name says: a
`metamath` line names set.mm's counterpart of the theorem, which is checked to
be a label set.mm has, and a `note` is prose for a person. Each is said at most
once, between the `theorem` line and the statement, and continues on lines
indented further than it. A `define` line states what its name is and is cited by its label, and the
`reads` line under it says in words what the name means. Both `reads` and the
`note` a block opener may carry are one line each, are the only prose a proof
holds, and are read by no tool: what is checked is that a define has a reading
and that a note belongs to a block. `SYNTAX.md` says why they exist and why
prose is allowed nowhere else.

A `let` line carries an **introduction**, not a formula. It names something and
says what it is, and the ten forms above are all of them. `⊆` introduces a
part of a set, which is a member of its power set: `let X ⊆ A` is read as
`X ∈ 𝒫A`, the name `for all X ⊆ A` quantifies over, and a line saying
X ⊆ A or X ∈ 𝒫A answers for the other. What it asserts
is only what `be` says of a function it names: `let g : Y → X be one-to-one`
asserts `g : Y → X is one-to-one`, and an item stating it asks a citation for
that line as it asks for a membership. The function's type is a declaration
and is not asked for. Its sets are those the citing proof gives the function
it stands for, so `let x ∈ D` beside `let f : D → E` asks, of a citation
naming a function on {0, …, 1}, that x be in {0, …, 1}. A codomain the item
names as a number system is asked for, though. For example, `product-real`
states `let t : {a, …, b} → ℝ`, so a proof citing it for a function declared
`t : {1, …, n} → ℕ` is answered, since ℕ is inside ℝ, and one declared
`t : {1, …, n} → ℂ` is refused. The plain function form takes a set after its arrow and
nothing else, so `let g : Y → X is one-to-one`, which fits it with "X is
one-to-one" for the set, is refused.
`∉` introduces a thing of the sort a set holds that is not in it, and `be an
element` a thing whose sort the text decides; neither claims the thing is a
set. The last says what a property is a property of, and never names the thing
it holds of, because that name comes from the notation that binds it: in
`{t ∈ X : P(t)}` the braces introduce `t`, and it does not exist above them.
Three of those, `be an element`, `be a set` and `be a point`, are not notations
and never appear inside a formula. `assume` does take a formula, because it
does assert. `thm:proofs/wiedijk/subsets/add-element-bijection` introduces its `a` by `∉`, and
`mun:stdlib/counting/card-singleton` and eight other items introduce theirs by `be an
element`. The kernel reads either as the thing being a set as well, since
`{a}` of a proper class is empty; that sethood is apparatus the page never
writes.

Quantifying over an arbitrary set is the formula-position counterpart, and it is
a notation: `for all sets X, ...`, declared in `corpus/db/notation.records` as a binder
with no domain. Ten lines in the corpus use one of these arbitrary forms, four
`be a set`, three `be a point` and three `for all sets`, and until they were
declared none of them matched anything.

## Names

An item is named by the file that holds it and its own name: its full name is
the file's path from the root without the extension, `/`, and the name on its
`theorem` or record line; a record's path is read from inside `corpus/`.
`corpus/stdlib/numbers.records` holds `stdlib/numbers/int-real`;
`proofs/wiedijk/triangle-inequality.proof` holds
`proofs/wiedijk/triangle-inequality/abs-bounds`. A name need only be unique within its
file.

`stdlib` is the one directory the rules name, because its modules are the
library's records files, `corpus/stdlib/<module>.records`, and hold items
rather than proofs. Any other module names a proof file, `<module>.proof`,
wherever under the root that file is kept.

**An import names one item, after the words its record's header says before
its name.** A proof file imports each item it uses from another file, one to a
line, by its full name, its paths in one column:

```proof
import axiom              stdlib/calculus/completeness
import theorem            stdlib/divisibility/prime-factor
import axiom              stdlib/numbers/trichotomy
import mundane theorem    stdlib/numbers/int-closure
import definition         stdlib/divisibility/gcd
import definition         stdlib/counting/C
import theorem            proofs/wiedijk/triangle-inequality/abs-bounds as abs-sum
import definition         tests/docs/tri/T as U (D1)
import definition         tests/docs/tri/B
```

The words are what the item is where it lives. For the library they are the
record's header: its kind, with `mundane` before it where the record is a
theorem marked mundane (`DATABASE.md`, "Record kinds"). For a proof file they
are `theorem` for a theorem and `definition` for a define outside the
theorems, whether or not the define takes an argument, since a reader calls
both "the definition of T" and "the definition of B". A define is never
mundane, in the library's proof files or anywhere else: it is where a name
gets its meaning, and a reader meets it there. A define of a phrase is
imported by the name before its colon and cited as a definition,
`def:<name>`, with no label on the import line. So the head of a file says what the file rests on, what each item is,
and which of it is taken for granted, without the reader opening another
file. There is no import of a whole file, and a bare `import` is a defect, as
is `import mundane` with no kind. The path is the full one from the root, so
moving or renaming a directory changes the imports and nothing else about
them.

**A citation writes the prefix its import's words give and the item's name,
not its path:** `mun:` where the words open with `mundane`, which only a
theorem's do, and the kind's prefix otherwise. The import says where an item comes from, so the step does
not say it again:

| record | citation |
|---|---|
| `axiom completeness` | `obtain c: axi:completeness S := S, from 5, 2, 7` |
| `axiom trichotomy` | `axi:trichotomy x := f(c), from H4, 13` |
| `theorem prime-factor` | `obtain p: thm:prime-factor m := n! + 1, from 2` |
| `mundane theorem int-closure` | `requires 10^k − 1 ∈ ℤ: mun:int-closure` |
| `definition C` | `def:C n := m, k := m + 1, from 5` |
| `definition gcd` | `def:gcd a := a, b := b` |

The prefix stays because it says on the line whether a reader needs to see
the step, which is what a viewer collapses by, and because it keeps an item's
name apart from a method's: `thm:induction` is a theorem and `induction` is
the method. The record says what the item is, which is what the elaborator
reads to decide whether to unfold it or cite it. A theorem of the citing file is cited
the same way, `thm:even-square`, and has no import. A notation, a method and
the defines of a cited theorem are imported by nothing.

**An imported define carries a label only where the file cites it.** The name,
`U` after `as` or the define's own, is what formulas write. The label, `(D1)`,
is what a line cites when it writes the define out, as a calculation link
does:

```proof
U(3) = 3(3 + 1)/2        D1
     = 6                 arithmetic
```

A chain line may cite a bare label, and a name of one capital letter would read as a label there, so the define is cited by a
label of the file's own and not by its name. A file that only writes `B` in
its formulas, and never writes B out, has nothing to cite and gives no label.
A label given and never cited is a defect, as is a citation of an imported
define whose import gives no label; the message for the second says to add
one. Like every label a file gives outside its theorems, a define's label is
used once in the file, and no theorem below reuses it. A library function is
applied bare in a formula, `gcd(a, b)`, and a step that unfolds it cites
`def:gcd`: the one import serves both.

**`as` gives an imported item a name of the file's own.** Every name a file
cites or applies is distinct within it: its own theorems, and each import under
its name or the name after `as`. Where two would share a name, an import takes
`as`, as the tests of the library do, whose theorems take the names of the
items they test: `import mundane theorem stdlib/numbers/abs-one as
numbers-abs-one`. An
imported define is written inside formulas, so the name it is imported under,
its own or the one `as` gives, is one letter, as a define's is. A library
function is imported by its own name and takes no `as`: a formula reads the
library's name for it wherever it is imported. Any other library item, and a
proof's theorem, are written only in a justification, and the name `as` gives
one may be any name.

A constant the page writes as a letter is that constant until a line
introduces a name with the same letter, if its notation is marked
`shadowed`; then, in that line's scope, the letter is the name. Two
constants are marked, the imaginary unit i and Euler's number e: a proof may
write `obtain i` or `Σ(i = 1 to n)` and mean its own i, and a group's
identity e, a walk `let e : {1, …, n} → E` or `let e = ⌊A + 1/2⌋ − A` is
the proof's own e, as a reader takes it. Which constants yield is decided
one at a time, since a letter a reader would not reuse is one the page
should not let them reuse.

**Each of these is a defect:** an item cited or applied and not imported; an
import that nothing cites or applies; an item imported twice; an import whose
words are not its record's header, and a citation whose prefix is not `mun:`
for a theorem taken for granted, or not the item's kind for any other item;
`mundane` before an axiom, a definition or a define; a citation
written with a path; an import of a path that names no file; an import of a
name the file does not hold, or holds only inside a theorem; an import of a
theorem of the importing file; an imported define's label that no line cites,
and a citation of an imported define whose import gives no label; and two
names alike, among the file's theorems and its imports.

The imports come before the first theorem and any define outside a theorem.
The imports of proof files' theorems and defines have no cycle, since what a
file imports is read before it; a library file imports nothing, and is read
before every proof.

A `define` may stand outside any theorem: before the first, or after a
theorem's last step, where that theorem could never use it. It belongs to
the file, and every theorem below it may use it, in its statement as well
as its proof. Two definitions of one name where both could be read are a
defect: two outside the theorems, one outside and one imported, two
imported, or a proof's own define under a name the file already gives
something. A definition means what it meant in the file that wrote it. A
theorem citing another file's theorem reads that theorem's definitions
there, needs none of them imported, and cannot capture one with a name of
its own.

## Steps

```grammar
<step>  ::= <number> `.` <claim> <justification> [ <note> ] { <requires> } [ <block> ]
<claim> ::= <formula> { <formula> }
<note>  ::= `note` <words>
```

The note is one line, allowed only where the justification opens a block, and
it says what the block is doing. A part marker such as `case` may be followed
by a note of its own, before the part's openers, saying what that part does.

Several formulas mean their conjunction, and **a period followed by whitespace,
or ending the claim, separates them**. Twenty-nine of the corpus's 280 claims
are more than one formula, and all 96 periods inside a claim are separators.

The claim runs from the step number until the first line whose first token is a
justification head, which is why a claim may not begin with one of those fifteen
tokens. No claim in the corpus does, and a parser rejects one that would. The
sixteenth head, a define's label, is a head only as a whole line, `D2` or `D2,
from 4.1`, and only where a define in scope carries it: a claim may well begin
with a capital, as `C ⊆ A` does.

A step numbered `p.n` belongs to the block of the step numbered `p`.

```grammar
<requires> ::= `requires` <formula> `:` <justification>
```

A requires line carries one citation and does not nest.

## Justifications

A justification is a head and a set of optional slots. The slots are:

| slot | written | 
|---|---|
| instantiation | `<name> := <term>` , comma-separated; a value runs to the comma that opens the next naming or the `from`, so it may hold commas of its own: `P := A, B, C are collinear, Q := x = 1` |
| names | `<name> { , <name> } :` , only after `obtain` |
| target | `in line <number>` \| `in <label>` |
| destination | `into line <number>` \| `into <label>` |
| source | `(line <number>)` \| `(<label>)` \| `(arithmetic)`, for an equation of numerals alone \| `(real arithmetic)`, for a closed equation with a square root |
| from | `from <ref> { , <ref> }` \| `from line <number>` |
| start | `starting at <term>` |

The eighteen heads and the slots each admits:

```grammar
<justification> ::=
    <prefix> <cited> [ <instantiation> ] [ `,` <from> ]
  | `obtain` <names> <prefix> <cited> [ <instantiation> ] [ `,` <from> ]
  | `obtain` <name> { `,` <name> } `from` ( `line` <number> | <label> )
  | `exhibit` `,` <from>
  | `substitute` <formula> <source> [ <destination> ]
  | `substitute` ( `line` <number> | <label> )    -- the equation that line says
  | `substitute`                                  -- rows follow
  | `instantiate` <instantiation> <target> [ `,` <from> ]
  | `algebra` [ `,` <from> ]
  | `arithmetic`
  | `real arithmetic`
  | `inequalities` [ `,` <from> ]                  -- with no `from`, rows may follow
  | `transitivity` `,` <from>
  | `antisymmetry` `,` <from>
  | `membership` [ `,` <from> ]
  | `inspection` [ `,` <from> ]
  | `join` <ref> { `,` <ref> }
  | `restate` <ref> { `,` <ref> }                 -- one line, with any defines that read its names
  | `contradiction`
  | `proof`
  | `induction` `on` <name> <start>
  | `cases` `,` <from>
  | `both directions`
  | `calculation`
  | <label> [ `,` <from> ]                         -- a define's label
<prefix> ::= `axi:` | `thm:` | `def:` | `mun:`
```

`join` and `restate` take their references directly and never the word `from`.

A define's label as the head says the claim is what the define names: the
name, applied or not, on one side and its value on the other. For a define by
cases the `from` lines say which case, by its condition or the condition's
negation.

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

`contradiction`, `proof`, `induction`, `cases` and `calculation` are justified by
a block. The block is the sub-steps numbered under the step, together with an
opening line or part markers as the method requires.

```grammar
<block> ::= [ <opener> ] { <part> | <step> }
<opener>::= `suppose` <formula> `(` <label> `)`          -- contradiction
          | <hypothesis> { <hypothesis> }                -- proof
<part>  ::= <part marker> [ <note> ] [ <hypothesis> ] { <step> }
<part marker> ::= `base` | `step` | `case`
```

A part marker is a bare word on its own line. Which markers a block may carry,
in which order, and whether a part opens with an assumption, are read from that
method's record in `corpus/db/methods.records`, not hard-coded: induction declares `base,
step`, and cases declares a repeating `case` whose parts open with `assume`.
An induction's `step` part opens with `let k ∈ X` and `assume step N is true
for k, the induction hypothesis (IH)`. The second writes no formula of its
own: what it assumes is step N's statement after "for all k ∈ X,", taken
from the tree of N's claim (`Opener::is_hypothesis`), and the k it names is
the letter that claim binds. Over the parts of a set, a claim "for all Y ⊆
X", it opens with `let Y ⊆ X`, the hypothesis, and `let a ∈ X ∖ Y`, the
member the step adds.

## Calculation chains

```grammar
<chain>      ::= <first line> { <chain line> }
<first line> ::= <term> <rel> <term> [ <modulus> ] <citation>
<chain line> ::= <rel> <term> [ <modulus> ] <citation>
<rel>        ::= `=` | `≤` | `<` | `≥` | `>` | `≡`
<modulus>    ::= `(mod` <term> `)`
<citation>   ::= <ref> | `arithmetic` | `real arithmetic` | <line reason>
<line reason> ::= `algebra` [ `,` <from> ]
               | `substitute` ( `line` <number> | <label> )
               | `instantiate` <instantiation> <target> [ `,` <from> ]
               | <prefix> <cited> [ <instantiation> ] [ `,` <from> ]
```

A line whose relation is `≡` says its modulus, `≡ 1·10 (mod 3)`, and no other
line does; the modulus is not part of the term the next line continues from,
so after `≡ 1·10 (mod 3)` the chain goes on from 1·10. Every `≡` line of a
chain says the same modulus, a chain with a `≡` has no order, and once a
line says `≡` every line after it does: a chain that has become a
congruence does not go back to `=`, so that no `=` after one reads as though
the chain had become an equation again.

The citation is separated from the term by two or more spaces in every chain
line. A parser should not rely on that. Read it by its words instead:

- The citation starts at the first word after the relation that opens a
  reason: `algebra`, `arithmetic`, `real arithmetic`, `substitute`,
  `instantiate`, or a cited item such as `def:odd`.
- Where no word opens a reason, the citation is the last word, a step
  number or a label.
- So a line ending `real arithmetic` cites that method, and its term does
  not end in "real".

A cited equation may face either way; the line says nothing about
which. `arithmetic` stands in
for a reference only on a line whose relation is between numerals alone, and
cites nothing: the fact is worked out where it stands (`SYNTAX.md`).
`real arithmetic` stands in the same way, on a line whose terms are closed,
or whose only changed pieces are, each worked out by real arithmetic.

A chain goes one way. Its orders are all `≤` and `<`, going up, or all `≥`
and `>`, going down, with `=` anywhere among either: a ≤ b ≥ c says nothing
of a against c, and is refused. A chain going down is a textbook's estimate,
2^(de) − 1 = (2^d)^e − 1 ≥ 2^d − 1 > 1, and is the same links read from its
last term going up, since a ≥ b is b ≤ a.

The claim's relation is `=` if every line is `=`; going up, `≤` if every
line is `=` or `≤`, and `<` if any line is `<`; going down, `≥` and `>` the
same way; and `≡` with the lines' modulus if any line is `≡`: 10^(m + 1) =
10^m·10 ≡ 1·10 ≡ 10 ≡ 1 (mod 3) concludes a congruence, never an equation. A `≡` line cites a line stating
exactly that congruence, as any line does, so a term is never replaced by a
congruent one inside an exponent, where congruence does not carry.

## Inequality rows

```grammar
<rows>      ::= <first row> <row> { <row> }
<first row> ::= <formula> <ref>
<row>       ::= <formula> <manipulation>
<manipulation> ::= `adding` <term> | `multiplying by` <term>
                 | `restate` | `weakening` | `algebra`
```

An `inequalities` justification with no `from` may be followed by its rows,
one to a line, each a formula and then its reason. The reason is read from
the right: the last word is a reference, `restate`, `weakening` or
`algebra`, or the line ends in `adding` or `multiplying by` and a term, and
the formula is what is left. Each formula is an order, an equation, a
disequality or the negation of an order, a sentence the parser reads; the
term after `adding` or `multiplying by` is read the same way. The first
row's reference is a line the step cites, and its only citation. What each
row may be, and that the last is the claim, is `METHODS.md`'s.

## Substitute rows

```grammar
<substitute rows> ::= <first row> <change row> { <change row> }
<change row>      ::= <formula> <line reason>
```

A bare `substitute` is followed by its rows, one to a line, each a formula
and then its reason.

- A row's reason is read the way a chain line's is.
- The first row's reason is a line the step cites, and that is the step's
  only citation.
- A later row's reason is never a bare line number or label. A row that
  puts in what a line says is `substitute line L`, or `substitute H3` for a
  label.
- What each row may be, and that the last is the claim, is in `METHODS.md`.

## Scope of a citation

A step numbered `a` may cite a step numbered `b` when `b` is an ancestor of `a`,
or `b` shares `a`'s path up to some position and comes before it there. Written
over the dotted components: `b` is in scope for `a` when `len(b) ≤ len(a)`,
`b[:-1] = a[:len(b)-1]`, and `b[-1] < a[len(b)-1]`. Steps inside a block that
has closed are not visible outside it, so `17.2` cannot cite `17.1.1` but can
cite `17.1`.

The parts of a block share its numbering, and a step in one part is not in
scope in another: in a `cases` block whose first case holds `1.1` and second
holds `1.2`, step `1.2` cannot cite `1.1`, which was shown under the first
case's assumption. Written over the parts: `b` is in scope for `a` as above,
and where `b` and the step above `a` at `b`'s depth are each in a part of
their block, it is the same part. A label declared by one part is likewise in
scope in that part alone (below), and so is a letter an `obtain` in it
introduces.

A label is in scope inside the block that declares it and nowhere else. A
theorem's hypothesis labels are in scope throughout its proof. So two sibling
blocks may use one label, as each of `binomial-step`'s `proof` blocks fixes k
as `(J)`, and a citation of it means the line of the block it sits in.

A letter is in scope where a label introducing it would be: a theorem's `let`
lines throughout, a block's `let` lines inside the block, an `obtain`'s letters
from its step on, and a define's name below the define. A requires line may
also write the letters its step's claim binds. A binder inside a formula, `for
all` or `there is`, holds its letter to the end of that formula, so in "For all
k ∈ ℕ₀, L(k) ∈ ℝ. U(k) ∈ ℝ." the second formula's k is introduced by nothing.
Both tools refuse a letter out of scope: the checker says so, and the
elaborator finds no name for it.

References cannot be found by scanning a line for digits. Claims are full of
numerals that look like step numbers: a square-root instantiation contains a 2
and an exponent contains a 1. A citation is recognised only by its position in
a parsed justification, never by pattern.

## Database records

```grammar
<record> ::= ( `mundane` `theorem` | <kind> ) <name> { <field> }
<kind>   ::= `notation` | `method` | `axiom` | `theorem` | `definition`
           | `precedence`
<field>  ::= <field name> <value>
```

`mundane` stands before `theorem` and before nothing else: a record headed
`mundane` alone, or `mundane` before any other kind, is a defect. Each kind has its own field names,
and a field outside them is refused:

| kind | fields |
|---|---|
| `notation` | `pattern`, `sort`, `level`, `assoc`, `commutes`, `identity`, `negates`, `spells`, `places`, `nests`, `bounds`, `joins`, `wraps`, `fills`, `repeats`, `shadowed`, `wanted`, `binds`, `reads`, `member`, `target`, `metamath`, `decided`, `note` |
| `method` | `form`, `block`, `parts`, `parts-repeat`, `part-opens`, `checks`, `decides`, `hypotheses`, `specified-in`, `metamath`, `note` |
| `axiom`, `theorem` | `metamath`, `target`, `open`, `note` |
| `definition` | `sort`, `builds`, `reads`, `metamath`, `target`, `open`, `symbol`, `defines`, `note` |
| `precedence` | the levels it declares |

`wanted` names the category a hole must want for the pattern to be read
there: the open interval is `(_, _)` read where a set is wanted, and nowhere
else.

The three kinds `axiom`, `theorem` and `definition` are the library's items,
and `DATABASE.md`, "Record kinds", says what each is to a reader and what the
mark means.

The tools read a field by its name, so a misspelt one is not that field: an
item whose `target` is spelt `taget` has no target, and every citation of it
would stop the build. `parse.FIELDS` holds the list and the checker reads
it.

A record begins at column 0; its fields are indented, one per line, and a field
value continues on further-indented lines. `#` at the start of a line is a
comment. An item's statement is written with the same `let`, `assume` and
`then` lines as a theorem header, so one parser reads both.

A record's `then` groups each take every hypothesis written above them, so a
definition carries two groups with a `let` between them where its second
sentence needs one more name than its first: a recursive definition's base
sentence takes no hypothesis and its step sentence takes one,
`def:stdlib/counting/factorial`. Clauses whose conditions differ are cases of
one sentence and not groups, `if k ∈ {0, …, n} then … . if n < k then … .`,
as in `def:stdlib/counting/C` (`DATABASE.md`, "Record kinds"). A function a
single proof needs of its own, such as the sum of the first m numbers, is not
a library item but a `define` in that proof.

A function the library offers is declared by a definition with a `sort` line,
by name and not by notation:

```records
definition gcd
  sort        number, number → number
  builds      _1 _2 cgcd co
  reads       the greatest common divisor of
  let a ∈ ℕ                                                           (H1)
  …
```

The record's name is the function's, and is letters only, since a formula
writes it; it may be a Greek letter, as `definition σ` is, and wherever the
elaborator writes the name into a Metamath file it spells the letter in
ASCII, `sigma`. `sort` says what the arguments and the value are, and the number of
places before its arrow is the number of arguments, so `definition gcd` with
`sort number, number → number` is applied as `gcd(_, _)`: a name applied to one
hole for each argument and nothing else, which is what keeps it from being
notation. `builds` is the set.mm term an application stands for, `_1` for the
first argument, since `target` already names the theorem the record's statement
is, and a definition with a `sort` line and no `builds` is refused. A `then`
line is optional: `min` and `max` have none, and what a proof needs of them is
in items of their own. A proof file that applies a function imports it as it
imports any item, after its record's header, from the library file that
declares it, with no label and no `as`:

```proof
import definition stdlib/divisibility/gcd
```

and then writes `gcd(a, b)`, which the parser reads as the name gcd applied to
a and b through the application patterns `corpus/db/notation.records`
declares for every function, `_(_)` and `_(_, _)`, as it reads a proof's
`T(k)`. The name's sort comes from the record wherever the file imports it
and the theorem gives the name none of its own, so a proof may still call a
point C. Applied without the import it is a defect, which the message says
how to mend; imported twice, imported with `as`, or imported and never
applied, it is one too. The library's own records import nothing, and every
library function is in scope in them.

A function's syntax is in its record and a notation's is in
`corpus/db/notation.records`. That is why a proof imports one and not the
other: a function's name is a letter or word a proof might give something of
its own, and a notation's tokens are not.

A name of several letters is read as one because the tokeniser takes the
library's function names as a second list beside the notations' words, both
read before any proof; a name that is also such a word is refused. A proof's
own function, a define with an argument, a sequence, a `let f : A → B` or a
define imported under a name, may not take the name of a library function
its file imports, so a reader never asks which gcd a line means; a file that
imports no C may call a function of its own C, and a set or a number with
that letter is no function and may be written anywhere.

## Not decided here

- **Whether a claim of several formulas can be cited one formula at a time.**
  `SYNTAX.md` lists this among its unsettled items. The grammar treats a step
  as one citable unit.
- **Everything inside a formula.** Notation, precedence, and the three
  different meanings of the vertical bar.
- **A `let … be the …` line, proposed and not built.** A theorem could name a
  thing by describing it, as a book does: `let D be the foot of the
  perpendicular from C to line AB`, `let c be the least upper bound of S`,
  `let ⊙O be the circle with centre O and radius r`. Each description would
  be a notation of its own, a term written in words (`the least upper bound
  of _`, whose target is `sup`), and the line would read as the naming `let`
  that takes the term, `let c = the least upper bound of S`. It adds nothing
  the page cannot say: a description with a term is a naming `let` today,
  and one without is an `obtain`, or a `let` with `assume` lines giving the
  facts that fix the thing. What it adds is readability, and one obligation:
  "the" says there is exactly one, so each description needs a record
  saying it names one thing where an `obtain` asks only that one exists.
  In `proofs/` it would change three steps, the foot of the altitude in
  `wiedijk/pythagoras` and the least upper bound in
  `wiedijk/intermediate-value` and `wiedijk/reals-uncountable`, and could
  reword about seventeen lines that name ⌊A/B⌋, a gcd or a min.
  `wiedijk/konigsberg`'s `let G be the undirected multigraph with …` is a
  special case of it already.
