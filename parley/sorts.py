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
from parse import Problem

NUMBER_SYSTEMS = {'ℕ', 'ℕ₀', 'ℤ', 'ℚ', 'ℝ'}

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
MEMBER = re.compile(r'^(\S+)\s*∈\s*(\S+)$')
KIND = re.compile(r'^(\S+)\s+be a (set|point)$')
FUNCTION = re.compile(r'^(\S+)\s*:\s*.+→.+$')
PROPERTY = re.compile(r'^(\S+)\s+be a property of the elements of\s+\S+$')
DEFINE = re.compile(r'^define\s+(\S+)\s*:=\s*(.+)$')
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
    out = {}
    for _, text, _, _ in thm.defines:
        m = DEFINE.match(LABEL.sub('', text).strip())
        if not m:
            continue
        g.sorts = sorts_in_scope(thm, g)
        try:
            out[m.group(1)] = parse(m.group(2), g)
        except Problem:
            continue
    return out


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

    out = {}
    for _, kind, text in sorted(events, key=lambda e: e[0]):
        if kind in ('let', 'assume', 'suppose'):
            found = _from_introduction(_body(text, kind))
            if found:
                out.setdefault(*found)
        elif kind == 'define':
            m = DEFINE.match(LABEL.sub('', text).strip())
            if not m:
                continue
            g.sorts = out
            try:
                sort = parse(m.group(2), g).sort
            except Problem:
                continue
            if sort not in (None, 'unknown', 'any'):
                out.setdefault(m.group(1), sort)
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
