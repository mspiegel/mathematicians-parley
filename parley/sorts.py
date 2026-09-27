"""Where a name's sort comes from.

GRAMMAR.md's "Sorts" section is the specification. A declaration is written on
the page, so this module first reads what the text states: a `let` line, the
claim of the `obtain` step that introduces a name, the right-hand side of a
`define`, or any numbered step claiming a membership. A membership gives a sort
there only when it names a number system, which is why the five number systems
are named below: it is the one place the tools know a notation by its text, and
it is here rather than in the parser because the rule is about what a
membership states, not about how a formula reads.

What those leave unknown, the kinds may settle (`kinds.py`): a set has the kind
of what it holds, so `let S ∈ 𝒫X` makes S a set though no number system is
named. A name neither reaches has no sort, which every hole accepts.
"""
import re

from formula import HOLDS, parse
from match import Rule, expand
from parse import Problem, Recursion, declined, define_parts

NUMBER_SYSTEMS = {'ℕ', 'ℕ₀', 'ℤ', 'ℚ', 'ℝ'}

# A label stands apart from what it labels, so `M(X)` ending a line is M
# applied to X and not a line labelled X.
LABEL = re.compile(r'\s+\([A-Z]+[0-9]*\)\s*$')
# `let x ∈ A` and `let a ∉ X`: a thing, and a set it is in or is not in.
MEMBERSHIP = re.compile(r'^(\S+)\s*∈\s*\S')
NOT_IN = re.compile(r'^(\S+)\s*∉\s*\S')
# `n ∈ ℕ`: a membership whose set is one name, which may say the sort.
NAMED_MEMBER = re.compile(r'^(\S+)\s*∈\s*(\S+)$')
KIND = re.compile(r'^(\S+)\s+be a (set|point)$')
# `let x be an element`: an element of nothing yet named.
ELEMENT = re.compile(r'^(\S+)\s+be\s+an\s+element$')
# `let P be a property of the elements of A`: the property, and its domain.
PROPERTY = re.compile(r'^(\S+)\s+be a property of the elements of\s+(\S+)$')
FUNCTION = re.compile(r'^(\S+)\s*:\s*.+→.+$')
# `let f : A → B be one-to-one`: a function's type, and a property of it.
FUNCTION_BEING = re.compile(r'^(\S+\s*:\s*.+→.+?)\s+be\s+(\S.*)$')
# `let X ⊆ A`: a part of a set.
PART = re.compile(r'^(\S+)\s*⊆\s*(\S.*)$')
# `let G be a finite group with operation · and identity e`: a set whose
# members are group elements, its operation, and its identity, which is one
# of them.
GROUP = re.compile(r'^(?P<group>\S+)\s+be\s+a\s+(?P<finite>finite\s+)?group'
                   r'\s+with\s+operation\s+(?P<operation>\S+)\s+and\s+'
                   r'identity\s+(?P<identity>\S+)$')
# `H is a subgroup of G`: a set of the group's elements.
SUBGROUP = re.compile(r'^(\S+)\s+is\s+a\s+subgroup\s+of\s+(\S+)$')


def let_formula(body):
    """A `let` body as the formula it asserts.

    `let f : A → B be one-to-one` introduces f and says it is one-to-one,
    and the formula is `f : A → B is one-to-one`: "be" is how English says
    "is" after "let". `let X ⊆ A` introduces a part of A, which is a member
    of its power set, and the formula is `X ∈ 𝒫A`, the one `for every X ⊆
    A` quantifies over. `let G be a finite group …` says G is finite; the
    rest of it names things and asserts nothing a proof cites. Every other
    body is read as it is written.
    """
    m = GROUP.match(body)
    if m and m.group('finite'):
        return f"{m.group('group')} is finite"
    m = FUNCTION_BEING.match(body)
    if m:
        return f'{m.group(1)} is {m.group(2)}'
    m = PART.match(body)
    if m:
        whole = m.group(2).strip()
        return f'{m.group(1)} ∈ 𝒫{whole if " " not in whole else f"({whole})"}'
    return body


SENTENCE = re.compile(r'(?<=[.])\s+')


def sentences(text):
    """The sentences of a line, each without its full stop.

    A sentence ends at a full stop followed by any space, a line break
    included, so a claim written across two lines splits where it would
    written on one.
    """
    pieces = (p.strip().rstrip('.').strip() for p in SENTENCE.split(text.strip()))
    return [p for p in pieces if p]


def _body(text, head):
    """A line without its keyword and without its trailing label."""
    return LABEL.sub('', text[len(head):].strip()).strip()


def _introduced(body, known):
    """The (name, sort) pairs a `let` body or a sentence states: none, one,
    or, for a group, the group and its identity. `known` is the sorts found
    so far, since a member of a group's set is a group element.
    """
    m = GROUP.match(body)
    if m:
        return [(m.group('group'), 'group-set'),
                (m.group('identity'), 'group-element')]
    m = SUBGROUP.match(body)
    if m:
        return [(m.group(1), 'group-set')]
    m = KIND.match(body)
    if m:
        return [(m.group(1), m.group(2))]
    m = PROPERTY.match(body)
    if m:
        return [(m.group(1), 'property')]
    m = FUNCTION.match(body)
    if m:
        return [(m.group(1), 'function')]
    m = NAMED_MEMBER.match(body)
    if m and m.group(2).rstrip('.') in NUMBER_SYSTEMS:
        return [(m.group(1), 'number')]
    if m and known.get(m.group(2).rstrip('.')) == 'group-set':
        return [(m.group(1), 'group-element')]
    return []


def definitions_in_scope(thm, g, sorts):
    """What each `define` line names, as a tree, read with the theorem's
    `sorts` (`sorts_in_scope`).

    A define asserts nothing; it abbreviates. So the name and the term are one
    formula wherever two formulas are compared, and this is the table that says
    which term each name stands for. A define may name something in terms of an
    earlier one, so the terms are read in the order they are written.

    A sequence defined by recursion has no term to stand for: its rule names
    the sequence itself, so it is never expanded, and a step that needs a
    value cites the define (`recursion_equation`).
    """
    out = file_definitions(thm, g)
    for _, text, _, _ in thm.defines:
        said = define_parts(text)
        if declined(said) or isinstance(said, Recursion):
            continue
        g.sorts = define_sorts(said, sorts)
        try:
            body = parse(said.body, g)
        except Problem:
            continue
        out[said.name] = (body if said.param is None
                          else Rule(said.param, body, said.domain))
    return out


def file_definitions(thm, g):
    """What each definition the theorem sees from outside it stands for:
    those its file writes above it and those its file imports.

    Each is written out in the file that wrote it, and nowhere else. A
    definition means what it meant there, whatever the reading file calls
    things: a file with a T of its own, or one that imported this T as U,
    reads the same rule, and a definition built from another is followed in
    the names of the file that built it.
    """
    if thm.scope is None:
        return {}
    return written_definitions(thm.scope, thm.line, g, frozenset())


def written_definitions(scope, line, g, seen):
    """`name -> tree` (a `match.Rule` for a function) for every definition
    a line of `scope`'s file at `line` may use, each written out.
    """
    out = {}
    for name, d, src in scope.visible(line):
        if (src.path, d[3]) in seen:
            continue          # an import cycle, which `check_imports` reports
        made = written_definition(d, src, g, seen | {(src.path, d[3])})
        if made is not None:
            out[name] = made
    return out


def written_definition(d, src, g, seen):
    """One definition, read and written out in the file that wrote it;
    None where its rule does not parse, which `check_formulas` reports.
    """
    said = define_parts(d[1])
    if declined(said):
        return None
    inner = written_definitions(src, d[3], g, seen)
    kept = g.sorts
    g.sorts = define_sorts(said, definition_sorts(inner))
    try:
        body = parse(said.body, g)
    except Problem:
        return None
    finally:
        g.sorts = kept
    body = expand(body, inner)
    return body if said.param is None else Rule(said.param, body, said.domain)


def definition_sorts(definitions):
    """The sort each definition gives its name: a function takes arguments,
    and any other is what its rule is.
    """
    out = {}
    for name, made in definitions.items():
        sort = 'function' if isinstance(made, Rule) else made.sort
        if sort not in (None, 'unknown', 'any'):
            out[name] = sort
    return out


def element_sort(domain, sorts=None):
    """The sort of what a define's domain holds: a number where the domain
    is a number system, what a name's sort says it holds where it says
    (`sorts`, a group's elements for a group's set), and otherwise none.
    """
    if domain.strip() in NUMBER_SYSTEMS:
        return 'number'
    return HOLDS.get((sorts or {}).get(domain.strip()))


def define_sorts(said, sorts):
    """The sorts a define's rule is read with: `sorts`, and for a function
    its parameter as what the domain holds.
    """
    if said.param is None:
        return sorts
    return {**sorts, said.param: element_sort(said.domain, sorts)}


def sorts_of_record(record, g):
    """The sort of every name an item's own lines state one for.

    A record keeps the keyword of a hypothesis in the field name where a proof
    line keeps it in the text, and a record has no steps and no `define`. That
    is the whole difference from `sorts_in_scope`, and what the lines leave
    unknown the kinds settle here as they do there: `let k ∈ {a, …, n}` names
    no number system, and k is a number because the range holds numbers.
    """
    out = {}
    for kind, value, _, _ in record.hypotheses:
        if kind in ('let', 'assume'):
            for found in _introduced(LABEL.sub('', value).strip(), out):
                out.setdefault(*found)
    # The parser's sorts are left as they were found: a record is read while
    # a proof that cites it is being read, and the proof's sorts are the ones
    # its next line is parsed with.
    kept, g.sorts = g.sorts, out
    from kinds import read_record, sort_of
    try:
        for name, kind in read_record(record, g).env.items():
            settle(out, name, sort_of(kind))
    finally:
        g.sorts = kept
    return out


def sorts_of_statement(thm):
    """The sort of every name a proved theorem's hypotheses state one for.

    What a citation of it reads: the statement, not the proof beneath. A
    proof line keeps its keyword in the text, which a record does not.
    """
    out = {}
    for kind, text, _, _ in thm.hypotheses:
        if kind in ('let', 'assume'):
            for found in _introduced(_body(text, kind), out):
                out.setdefault(*found)
    return out


def sorts_in_scope(thm, g):
    """The sort of every name the theorem states one for.

    The lines are read in the order they are written, because a `define` takes
    its sort from its right-hand side and that side may name something an
    earlier line introduced.
    """
    events = []
    for kind, text, _, no in thm.hypotheses:
        events.append((no, kind, text))
    for step in thm.steps:
        for kind, text, _, no, _ in step.openers:
            events.append((no, kind, text))
        events.append((step.line, 'claim', ' '.join(step.claim)))
    for kind, text, _, no in thm.defines:
        events.append((no, kind, text))

    # What the theorem sees from outside it is there before its first line.
    out = definition_sorts(file_definitions(thm, g))
    for _, kind, text in sorted(events, key=lambda e: e[0]):
        if kind in ('let', 'assume', 'suppose'):
            for found in _introduced(_body(text, kind), out):
                out.setdefault(*found)
        elif kind == 'define':
            said = define_parts(text)
            if declined(said):
                continue
            # A define with an argument is a function, whatever its rule
            # gives, and `S(n)` is then S applied to n and not S times n. A
            # sequence defined by recursion is one too.
            if isinstance(said, Recursion):
                for name in said.names:
                    out.setdefault(name, 'function')
                continue
            if said.param is not None:
                out.setdefault(said.name, 'function')
                continue
            g.sorts = out
            try:
                sort = parse(said.body, g).sort
            except Problem:
                continue
            if sort not in (None, 'unknown', 'any'):
                out.setdefault(said.name, sort)
        else:
            for sentence in sentences(text):
                for found in _introduced(sentence, out):
                    out.setdefault(*found)
    # What the lines above leave unknown, the kinds may settle: `let S ∈ 𝒫X`
    # names no number system, and S is a set because what 𝒫X holds is sets.
    # Read with the sorts found so far, and only where they found none.
    # Imported here: `kinds` parses with the sorts this module gives it.
    g.sorts = out
    from kinds import read_theorem, sort_of
    for name, kind in read_theorem(thm, g).env.items():
        settle(out, name, sort_of(kind))
    g.sorts = out
    return out


def settle(out, name, settled):
    """Put the sort the kinds settle for `name` into `out`, where the lines
    found none, or found only `set` and the kinds say what the set holds:
    `let K be a set` with K's members read as sets makes `|Y|`, for Y in K,
    a size.
    """
    if not settled:
        return
    if out.get(name) == 'set' and settled in HOLDS:
        out[name] = settled
    out.setdefault(name, settled)
