# Grammar of the skeleton

`SYNTAX.md` says what a step must contain and why each form was chosen.
`DATABASE.md` says where things are stored. This document says how the stored
text is read: the line kinds, the justification forms, and the rules a parser
applies. It is written from the ten proofs in `proof/` and the three database
files in `db/`, and every rule below holds on all of them.

It covers the **skeleton only**. A claim is an opaque run of text here. Giving
that text structure is a second grammar, for notation and precedence, which is
not written and not needed to check anything in this document.

Every production below was run against the corpus while this was written. All
246 justifications match a declared production, all 22 labels match their
pattern, the only part markers are the three declared, and no step is numbered
under a parent that does not exist. Two rules were wrong on the first pass and
are corrected here: item names are not all lowercase, and `obtain` has two
forms rather than one.

Notation used below: `<x>` a named part, `[x]` optional, `{x}` zero or more,
`a | b` alternatives. Literal text is in `code`.

## Lexical rules

Files are UTF-8 in Normalisation Form C. An implementation works in Unicode
scalar values; UTF-16 is used nowhere, for the reason in `DATABASE.md`. Every
non-ASCII character in a claim must appear in `db/notation.db`, which doubles
as a whitelist.

- `<label>` is `[A-Z]+[0-9]*`, written in parentheses at the end of the
  declaration and cited bare. Observed: H1, S, K2, IH, C1, D1. When the
  declaration is continued over several lines the label sits at the end of the
  last of them, as the eleventh hypothesis of the Bezout lemma does, so labels
  cannot be collected without applying the continuation rule first.
- `<number>` is a step number: one or more integers joined by dots, `1`,
  `1.1`, `17.25.5.10`.
- `<ref>` is a `<number>` or a `<label>`.
- `<name>` is `[A-Za-z][A-Za-z0-9-]*`, as in `least-upper-bound` and `nat0-closure`.
  Almost every name is lowercase words joined by hyphens. Two are a single
  capital, `def:S` and `def:G`, which take the letter of the function they
  define. Validating this grammar against the corpus found that case and
  nothing else, so the rule is written to admit it rather than to rename the
  two items.
- `<term>` and `<formula>` are opaque runs of text, delimited only by the rules
  below. The parser does not look inside them.

Horizontal whitespace is not significant and carries no structure. Indentation
is presentation: steps at the same depth begin at column 10 in one file and 11
in another. Structure comes from the step number. The single exception is the
chain line, noted below.

## Files

```
<proof file>  ::= { <theorem> }
<theorem>     ::= `theorem` <name>
                  { <hypothesis> }
                  <conclusion>
                  { <define> | <step> }
<hypothesis>  ::= ( `let` <formula> | `assume` <formula> ) `(` <label> `)`
<conclusion>  ::= `then` <formula>
<define>      ::= `define` <name> `:=` <term> `(` <label> `)`
```

Theorems appear in dependency order, so every pointer resolves to something
earlier. A `define` line claims nothing and is cited by its label.

## Steps

```
<step>  ::= <number> `.` <claim> <justification> { <requires> } [ <block> ]
<claim> ::= <formula> { <formula> }
```

Several formulas mean their conjunction. The claim runs from the step number
until the first line whose first token is a justification head, which is why a
claim may not begin with one of those fifteen tokens. No claim in the corpus
does, and a parser rejects one that would.

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
| target | `in line <number>` \| `in <label>` \| `in def:`<name> |
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
  | `lines` <ref> { `,` <ref> }
  | `contradiction`
  | `fix`
  | `induction` `on` <name> <start> `,` <from>
  | `cases` `,` <from>
  | `calculation`
```

`lines` takes its references directly and never the word `from`.

`obtain` has two forms. With an item it names its objects with a colon, as in
`obtain q, r: thm:division-algorithm n := c, d := d, from H3, H4`. Without one
it takes a single name and a line, as in `obtain δ from line 17.4`. The second
form is written in `SYNTAX.md` as `obtain a, from L`, with a comma and a bare
reference; the corpus writes no comma and `from line`. The corpus form is the
one recorded here, and `SYNTAX.md` should be corrected to match it.

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
<kind>   ::= `notation` | `method` | `definition` | `theorem`
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

- **What `instantiate` may target.** Its target slot takes a line, a label,
  and twice an item, as in `instantiate u := b in def:least-upper-bound`. This
  sits badly beside the rule in `SYNTAX.md` that `from` lists lines and nothing
  else. Either the grammar says plainly that the target slot and the `from`
  slot admit different things, which is the reading written above, or those two
  citations change to a step that cites the definition first. The grammar
  above permits the item form so that the corpus parses; the language decision
  is open.
- **Whether a claim of several formulas can be cited one formula at a time.**
  `SYNTAX.md` lists this among its unsettled items. The grammar treats a step
  as one citable unit.
- **Everything inside a formula.** Notation, precedence, and the three
  different meanings of the vertical bar.
