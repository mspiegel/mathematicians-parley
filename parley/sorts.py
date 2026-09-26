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

from formula import parse
from match import Rule, expand
from parse import Problem, declined, define_parts

NUMBER_SYSTEMS = {'ℕ', 'ℕ₀', 'ℤ', 'ℚ', 'ℝ'}

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
MEMBER = re.compile(r'^(\S+)\s*∈\s*(\S+)$')
KIND = re.compile(r'^(\S+)\s+be a (set|point)$')
FUNCTION = re.compile(r'^(\S+)\s*:\s*.+→.+$')
PROPERTY = re.compile(r'^(\S+)\s+be a property of the elements of\s+\S+$')
SENTENCE = re.compile(r'(?<=[.])\s+')


def _body(text, head):
    """A line without its keyword and without its trailing label."""
    return LABEL.sub('', text[len(head):].strip()).strip()


def _from_introduction(body):
    """The sort a `let` body or a membership sentence states, or None."""
    m = KIND.match(body)
    if m:
        return m.group(1), m.group(2)
    m = PROPERTY.match(body)
    if m:
        return m.group(1), 'property'
    m = FUNCTION.match(body)
    if m:
        return m.group(1), 'function'
    m = MEMBER.match(body)
    if m and m.group(2).rstrip('.') in NUMBER_SYSTEMS:
        return m.group(1), 'number'
    return None


def definitions_in_scope(thm, g):
    """What each `define` line names, as a tree.

    A define asserts nothing; it abbreviates. So the name and the term are one
    formula wherever two formulas are compared, and this is the table that says
    which term each name stands for. A define may name something in terms of an
    earlier one, so the terms are read in the order they are written.
    """
    out = file_definitions(thm, g)
    for _, text, _, _ in thm.defines:
        said = define_parts(text)
        if declined(said):
            continue
        g.sorts = sorts_in_scope(thm, g)
        if said.param is not None:
            g.sorts = {**g.sorts, said.param: element_sort(said.domain)}
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
    g.sorts = definition_sorts(inner)
    if said.param is not None:
        g.sorts[said.param] = element_sort(said.domain)
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


def element_sort(domain):
    """The sort of what a define's domain holds: a number where the domain
    is a number system, and otherwise none said here.
    """
    return 'number' if domain.strip() in NUMBER_SYSTEMS else None


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
            found = _from_introduction(LABEL.sub('', value).strip())
            if found:
                out.setdefault(*found)
    # The parser's sorts are left as they were found: a record is read while
    # a proof that cites it is being read, and the proof's sorts are the ones
    # its next line is parsed with.
    kept, g.sorts = g.sorts, out
    from kinds import read_record, sort_of
    try:
        for name, kind in read_record(record, g).env.items():
            settled = sort_of(kind)
            if settled:
                out.setdefault(name, settled)
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
            found = _from_introduction(_body(text, kind))
            if found:
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
            found = _from_introduction(_body(text, kind))
            if found:
                out.setdefault(*found)
        elif kind == 'define':
            said = define_parts(text)
            if declined(said):
                continue
            # A define with an argument is a function, whatever its rule
            # gives, and `S(n)` is then S applied to n and not S times n.
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
            for sentence in SENTENCE.split(text.strip()):
                found = _from_introduction(sentence.strip().rstrip('.').strip())
                if found:
                    out.setdefault(*found)
    # What the lines above leave unknown, the kinds may settle: `let S ∈ 𝒫X`
    # names no number system, and S is a set because what 𝒫X holds is sets.
    # Read with the sorts found so far, and only where they found none.
    # Imported here: `kinds` parses with the sorts this module gives it.
    g.sorts = out
    from kinds import read_theorem, sort_of
    for name, kind in read_theorem(thm, g).env.items():
        settled = sort_of(kind)
        if settled:
            out.setdefault(name, settled)
    g.sorts = out
    return out
