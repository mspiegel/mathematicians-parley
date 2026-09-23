"""Where a name's sort comes from.

GRAMMAR.md's "Sorts" section is the specification. Every sort is written on the
page, so this module only reads what the text states: a `let` line, the claim
of the `obtain` step that introduces a name, the right-hand side of a `define`,
or any numbered step claiming a membership. Nothing here guesses, and a name
these four sources do not reach simply has no sort, which every hole accepts.

The sorts are flat, so a set carries no sort for its elements and a membership
gives a sort only when it names a number system. That is why the five number
systems are named below. It is the one place the tools know a notation by its
text, and it is here rather than in the parser because the rule is about what a
membership states, not about how a formula reads.
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


def sorts_of_record(record):
    """The sort of every name an item's own lines state one for.

    A record keeps the keyword of a hypothesis in the field name where a proof
    line keeps it in the text, and a record has no steps and no `define`. That
    is the whole difference from `sorts_in_scope`.
    """
    out = {}
    for kind, value, _, _ in record.hypotheses:
        if kind in ('let', 'assume'):
            found = _from_introduction(LABEL.sub('', value).strip())
            if found:
                out.setdefault(*found)
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
    g.sorts = out
    return out
