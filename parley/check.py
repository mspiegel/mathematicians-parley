#!/usr/bin/env python3
"""Check the corpus against GRAMMAR.md.

Reports the grammar, the numbering, block structure, pointer resolution, the
scope of every citation, calculation chains, that every formula on the page
parses one way, that a citation supplies the hypotheses of what it cites, and
that its claim is what that item concludes. It does not build the kernel proof;
that needs the elaborator.

Usage:  parley/check.py [root]
Exits non-zero when anything is reported.
"""
import re
import sys
import unicodedata
from pathlib import Path

import targets

sys.path.insert(0, str(Path(__file__).resolve().parent))
from formula import Grammar, parse
from match import (
    PROPERTY,
    binding_context,
    binding_sites,
    expand,
    instantiation,
    match,
    names,
    substitute,
)
from parse import (
    BLOCK_HEADS,
    HEADS,
    LABEL,
    NAME,
    NUMBER,
    PART_MARKERS,
    REF,
    Problem,
    check_encoding,
    fmt,
    parse_database,
    parse_proof,
)
from sorts import (
    FUNCTION,
    KIND,
    definitions_in_scope,
    sorts_in_scope,
    sorts_of_record,
)
from sorts import (
    LABEL as LABEL_AT_END,
)

# The productions of GRAMMAR.md, one per justification form.
INST = r'(?:[^\s,]+\s*:=\s*.+?)(?:,\s*[^\s,]+\s*:=\s*.+?)*'
FROM = rf'from\s+{REF}(?:\s*,\s*{REF})*'
PRODUCTIONS = {
    'citation':      rf'^(?:def|thm):{NAME}(?:\s+{INST})?(?:,\s*{FROM})?$',
    'obtain-item':   rf'^obtain\s+\S+(?:\s*,\s*\S+)*:\s*(?:def|thm):{NAME}'
                     rf'(?:\s+{INST})?,\s*{FROM}$',
    'obtain-line':   rf'^obtain\s+\S+(?:\s*,\s*\S+)*\s+from\s+'
                     rf'(?:line\s+{NUMBER}|{LABEL})$',
    'exhibit':       rf'^exhibit,\s*{FROM}$',
    'substitute':    rf'^substitute\s+.+?\s*\((?:line\s+{NUMBER}|{LABEL})\)'
                     rf'(?:\s+into\s+(?:line\s+{NUMBER}|{LABEL}))?'
                     r'(?:,\s*right to left)?$',
    'instantiate':   rf'^instantiate\s+{INST}\s+in\s+(?:line\s+{NUMBER}|{LABEL})'
                     rf'(?:,\s*{FROM})?$',
    'algebra':       rf'^algebra(?:,\s*{FROM})?$',
    'arithmetic':    r'^arithmetic$',
    'inequalities':  rf'^inequalities(?:,\s*{FROM})?$',
    'join':          rf'^join\s+{REF}(?:\s*,\s*{REF})*$',
    'contradiction': r'^contradiction$',
    'fix':           r'^fix$',
    'induction':     rf'^induction\s+on\s+\S+\s+starting\s+at\s+\S+,\s*{FROM}$',
    'cases':         rf'^cases,\s*{FROM}$',
    'calculation':   r'^calculation$',
}

# Methods whose steps this checker accepts without examining them.
CLOSURE = ('algebra', 'arithmetic', 'inequalities', 'join')

# A variable may be a Greek letter and may carry a subscript or a prime. These
# are not notation and have no record of their own; see GRAMMAR.md.
IDENTIFIER_CHARACTERS = set(
    'αβγδεζηθικλμνξοπρστυφχψω'
    'ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ'
    '₀₁₂₃₄₅₆₇₈₉′'
)

RELATIONS = ('=', '≤', '<')


class Report:
    def __init__(self):
        self.problems = []
        self.trusted = []

    def say(self, path, line, message):
        self.problems.append(Problem(path, line, message))

    def trust(self, path, line, method, number):
        self.trusted.append((path, line, method, number))


# ------------------------------------------------------------------ scope

def requires_refs(text):
    """What a requires line's justification cites."""
    m = re.search(r'\bfrom\s+(.*)$', text)
    if not m:
        return [], None
    out = []
    for tok in m.group(1).split(','):
        tok = tok.strip()
        if re.fullmatch(REF, tok):
            out.append(tok)
        elif tok:
            return out, tok
    return out, None


def in_scope(cited, here):
    """A step numbered `cited` is visible from the step numbered `here` when it
    is an ancestor, or shares `here`'s path to some position and comes before
    it there. Steps inside a closed block are not visible outside it.
    """
    if len(cited) > len(here):
        return False
    return cited[:-1] == here[:len(cited) - 1] and cited[-1] < here[len(cited) - 1]


def labels_in_scope(thm, step):
    """Hypothesis labels hold throughout a proof. A label declared by a block
    holds inside that block only. When the block has parts, a label declared by
    one part holds in that part alone, so one case of a case analysis cannot
    cite the assumption of another.
    """
    out = {lab: ('hypothesis', no) for _, _, lab, no in thm.hypotheses if lab}
    for _, _, lab, no in thm.defines:
        if no < step.line:
            out[lab] = ('define', no)
    by_number = {s.number: s for s in thm.steps}
    for other in thm.steps:
        k = len(other.number)
        if other.number != step.number[:k] or other.number == step.number:
            continue
        child = by_number.get(step.number[:k + 1])
        for _, _, lab, no, part in other.openers:
            if lab is None:
                continue
            if part is None or (child is not None and child.part == part):
                out[lab] = ('block', no)
    return out


# ------------------------------------------------------------------ checks

def check_characters(report, path, text, allowed):
    for no, line in enumerate(text.split('\n'), 1):
        for ch in line:
            if ord(ch) < 128 or ch in allowed:
                continue
            name = unicodedata.name(ch, 'unnamed')
            report.say(path, no,
                       f'character {ch!r} (U+{ord(ch):04X}, {name}) is in no '
                       f'record of db/notation.records')
            return


def check_database(report, records):
    seen = {}
    for r in records:
        key = (r.kind if r.kind in ('notation', 'method') else 'item', r.name)
        if key in seen:
            report.say(r.path, r.line,
                       f'{r.kind} {r.name} is already defined at line {seen[key]}')
        seen[key] = r.line
        for name, no in r.repeats:
            report.say(r.path, no,
                       f'{r.kind} {r.name} states {name} a second time; the '
                       f'two are joined into one field, so the second is not '
                       f'read on its own and saying it changes nothing')
        if r.kind in ('definition', 'theorem'):
            sources = [f for f in ('proved-in', 'metamath', 'open') if f in r.fields]
            if not sources:
                report.say(r.path, r.line,
                           f'{r.name} says neither where it is proved, nor which '
                           f'set.mm label supplies it, nor that it is open')
            if 'proved-in' in r.fields and (r.hypotheses or r.conclusions):
                report.say(r.path, r.line,
                           f'{r.name} is proved in a proof file but also carries a '
                           f'statement here; the statement must have one home')
            if ('proved-in' not in r.fields and not r.conclusions
                    and 'open' not in r.fields):
                report.say(r.path, r.line, f'{r.name} has no `then` line')
        if r.kind == 'method' and 'parts' in r.fields:
            for part in re.split(r',\s*', r.fields['parts']):
                word = part.strip().split()[0] if part.strip() else ''
                if word and word not in PART_MARKERS:
                    report.say(r.path, r.line,
                               f'method {r.name} declares part {word!r}, which is '
                               f'not a part marker')


TERM_SORTS = {'number', 'set', 'point', 'any'}
SORT_NAMES = {'number', 'set', 'point', 'formula', 'function', 'property',
              'variable', 'any'}


def check_notation(report, records):
    """A notation record declares a pattern, the sort of each hole, and what it
    yields. Two things follow mechanically and are checked here.
    """
    for r in records:
        if r.kind != 'notation':
            continue
        raw = r.fields.get('pattern')
        if not raw:
            report.say(r.path, r.line, f'notation {r.name} declares no pattern')
            continue
        patterns = re.split(r'\s{2,}', raw.strip())
        holes = [h.strip() for h in r.fields.get('holes', '').split(',') if h.strip()]
        yields = r.fields.get('yields', '').strip()

        # Every pattern of one record takes the same holes, so they must agree
        # on how many there are.
        counts = {p.count('_') for p in patterns}
        want = 0 if holes == ['none'] else len(holes)
        if counts != {want}:
            report.say(r.path, r.line,
                       f'notation {r.name} declares {want} hole(s) but its '
                       f'pattern(s) have {sorted(counts)}')

        # A `target` says what each pattern builds, one entry per pattern, so
        # the two lists have to line up and every hole has to be used. What
        # the entries name is checked against set.mm, which is not read here.
        if 'target' in r.fields:
            entries = [e.strip() for e in r.fields['target'].split(',')
                       if e.strip()]
            if len(entries) != len(patterns):
                report.say(r.path, r.line,
                           f'notation {r.name} has {len(patterns)} pattern(s) '
                           f'but {len(entries)} target entr(ies)')
            for entry in entries:
                if entry == 'folded':
                    continue
                used = {int(n) for n in re.findall(r'_(\d+)', entry)}
                if any(n < 1 or n > want for n in used):
                    report.say(r.path, r.line,
                               f'notation {r.name} target {entry!r} names a '
                               f'hole outside 1 to {want}')
                elif used != set(range(1, want + 1)):
                    report.say(r.path, r.line,
                               f'notation {r.name} target {entry!r} leaves a '
                               f'hole out')

        # Associativity is needed exactly when the pattern can nest in itself:
        # both edges are holes, and what it yields fits those holes.
        for p in patterns:
            edges = p.startswith('_') and p.endswith('_')
            nests = yields in holes or (yields in TERM_SORTS and 'any' in holes)
            if edges and nests and 'assoc' not in r.fields:
                report.say(r.path, r.line,
                           f'notation {r.name} has a hole at each edge and '
                           f'yields {yields}, so {p!r} can nest in itself and '
                           f'is ambiguous without an assoc')
            if not (edges and nests) and 'assoc' in r.fields:
                report.say(r.path, r.line,
                           f'notation {r.name} declares an assoc it does not '
                           f'need: {p!r} cannot nest in itself')


def check_justification_form(report, path, just):
    if not any(re.match(p, just.text) for p in PRODUCTIONS.values()):
        report.say(path, just.line,
                   f'justification matches no production in GRAMMAR.md: '
                   f'{just.text[:64]!r}')
        return False
    return True


def check_numbering(report, thm):
    seen = set()
    for step in thm.steps:
        n = step.number
        if n in seen:
            report.say(thm.path, step.line, f'step {fmt(n)} is numbered twice')
        if len(n) > 1 and n[:-1] not in seen:
            report.say(thm.path, step.line,
                       f'step {fmt(n)} is numbered under {fmt(n[:-1])}, which does '
                       f'not exist')
        seen.add(n)


def check_blocks(report, thm, methods):
    for step in thm.steps:
        has_children = any(s.number[:-1] == step.number for s in thm.steps)
        head = step.just.head if step.just else None
        method = methods.get(head)
        wants_block = head in BLOCK_HEADS
        if wants_block and not has_children and head != 'calculation':
            report.say(thm.path, step.line,
                       f'step {fmt(step.number)} is justified by {head}, which '
                       f'needs a block, and has no sub-steps')
        if has_children and not wants_block:
            report.say(thm.path, step.line,
                       f'step {fmt(step.number)} has sub-steps but its '
                       f'justification {head} takes no block')
        declared = []
        if method and 'parts' in method.fields:
            declared = [p.strip().split()[0]
                        for p in re.split(r',\s*', method.fields['parts']) if p.strip()]
        found = [p for p, _ in step.parts]
        if declared and not found and has_children:
            report.say(thm.path, step.line,
                       f'step {fmt(step.number)} cites {head}, whose block carries '
                       f'the parts {", ".join(declared)}, and has no part markers')
        for marker, no in step.parts:
            if not declared:
                report.say(thm.path, no,
                           f'part marker {marker!r} under a {head} block, which '
                           f'declares no parts')
            elif marker not in declared:
                report.say(thm.path, no,
                           f'part marker {marker!r} is not one of the parts '
                           f'{", ".join(declared)} that {head} declares')
        if head == 'contradiction':
            if not any(k == 'suppose' for k, _, _, _, _ in step.openers):
                report.say(thm.path, step.line,
                           f'step {fmt(step.number)} is a contradiction whose block '
                           f'does not open with `suppose`')
        if head == 'fix':
            if not any(k in ('let', 'assume') for k, _, _, _, _ in step.openers):
                report.say(thm.path, step.line,
                           f'step {fmt(step.number)} is a fix whose block does not '
                           f'open with `let` or `assume`')
        if method and method.fields.get('part-opens') == 'assume, labelled':
            for index, (marker, no) in enumerate(step.parts):
                if not any(k == 'assume' and p == index
                           for k, _, _, _, p in step.openers):
                    report.say(thm.path, no,
                               f'the {marker!r} part of step {fmt(step.number)} does '
                               f'not open with a labelled `assume`')


def check_chain(report, thm, step):
    """A calculation only joins. Every line cites a numbered step or a label and
    carries no reasoning of its own, so a line that names an item or instantiates
    one is carrying a justification that belongs in a step.
    """
    if step.just.head != 'calculation':
        return
    if not step.just.chain:
        report.say(thm.path, step.line,
                   f'step {fmt(step.number)} is a calculation with no chain')
    for text, no in step.just.chain:
        if re.search(r'\b(?:def|thm):', text) or ':=' in text:
            report.say(thm.path, no,
                       'a chain line carries a justification; a calculation only '
                       'joins, so each line cites a numbered step or a label and '
                       'the reasoning lives in that step')
        if not any(text.lstrip().startswith(r) or f' {r} ' in text for r in RELATIONS):
            report.say(thm.path, no, 'chain line carries no relation')


def claims_of(thm):
    """Every line's claim, by the reference that names it."""
    out = {fmt(s.number): ' '.join(s.claim) for s in thm.steps}
    for _, text, lab, _ in thm.hypotheses:
        if lab:
            out[lab] = text
    for s in thm.steps:
        for _, text, lab, _, _ in s.openers:
            if lab:
                out[lab] = text
    return out


def check_citations(report, thm, items, methods, notation):
    numbers = {s.number for s in thm.steps}
    for step in thm.steps:
        just = step.just
        if just is None:
            continue
        scope = labels_in_scope(thm, step)
        if just.bad_ref is not None:
            report.say(thm.path, just.line,
                       f'`from` names {just.bad_ref!r}, which is neither a line '
                       f'nor a label')
        for ref in just.refs:
            if re.fullmatch(LABEL, ref):
                if ref not in scope:
                    report.say(thm.path, just.line,
                               f'step {fmt(step.number)} cites {ref}, which is not '
                               f'in scope here')
                continue
            cited = tuple(int(x) for x in ref.split('.'))
            if cited not in numbers:
                report.say(thm.path, just.line,
                           f'step {fmt(step.number)} cites line {ref}, which does '
                           f'not exist')
            elif not in_scope(cited, step.number):
                report.say(thm.path, just.line,
                           f'step {fmt(step.number)} cites line {ref}, which is '
                           f'inside a block that has closed')
        if just.target and just.target.startswith('def:'):
            report.say(thm.path, just.line,
                       f'step {fmt(step.number)} instantiates {just.target}; the '
                       f'target of instantiate is a line or a label, never an item')
        if just.head.startswith(('def:', 'thm:')):
            kind, name = just.head.split(':', 1)
            item = items.get(name)
            if item is None:
                report.say(thm.path, just.line, f'{just.head} resolves to no item')
            elif item.kind != ('definition' if kind == 'def' else 'theorem'):
                report.say(thm.path, just.line,
                           f'{just.head} names a {item.kind}')
        elif just.head not in methods:
            report.say(thm.path, just.line,
                       f'{just.head} is in no record of db/methods.records')
        for _, text, no in step.requires:
            heads = [h for h in HEADS if text.startswith(h)]
            if not heads and not re.match(rf'^from\s+{REF}$', text):
                report.say(thm.path, no,
                           f'requires line justified by {text[:40]!r}, which is '
                           f'neither a method, an item, nor a line')
            # A requires line cites an item like any other citation, so its
            # pointer resolves and its prefix matches the item's kind.
            m = re.match(rf'^(def|thm):({NAME})', text)
            if m:
                item = items.get(m.group(2))
                if item is None:
                    report.say(thm.path, no,
                               f'{m.group(0)} resolves to no item')
                elif item.kind != ('definition' if m.group(1) == 'def' else 'theorem'):
                    report.say(thm.path, no, f'{m.group(0)} names a {item.kind}')
            refs, bad = requires_refs(text)
            if bad is not None:
                report.say(thm.path, no,
                           f'`from` names {bad!r}, which is neither a line nor a label')
            for ref in refs:
                if re.fullmatch(LABEL, ref):
                    if ref not in scope:
                        report.say(thm.path, no,
                                   f'requires line cites {ref}, which is not in '
                                   f'scope here')
                    continue
                cited = tuple(int(x) for x in ref.split('.'))
                if cited not in numbers:
                    report.say(thm.path, no,
                               f'requires line cites line {ref}, which does not exist')
                elif not in_scope(cited, step.number):
                    report.say(thm.path, no,
                               f'requires line cites line {ref}, which is inside a '
                               f'block that has closed')
        if just.head in CLOSURE:
            report.trust(thm.path, just.line, just.head, fmt(step.number))


OBTAIN_NAMES = re.compile(r'^obtain\s+([^:]+?)(?::|\s+from)')
# `for every` and `there is` open a scope. The corpus capitalises either at the
# start of a sentence, so this is deliberately case-insensitive.
BINDER = re.compile(r'(?:for every|there is(?: no)?)\s+([A-Za-zα-ω][₀-₉′]*)\s*∈',
                    re.IGNORECASE)
# Named VARNAME rather than NAME: `NAME` is imported from parse and is the
# pattern for an item name, and shadowing it silently breaks every check that
# builds a regex from it.
VARNAME = re.compile(r'(?<![A-Za-zα-ω])([A-Za-zα-ω][₀-₉′]*)(?![A-Za-zα-ω])')
PAIR = re.compile(r'([^\s,]+)\s*:=\s*([^,]+?)(?=,\s*[^\s,]+\s*:=|,\s*from|\s+in |$)')


# Patterns whose holes sit next to each other with no token between them, so
# that the names filling them run together in the text.
ADJACENT_HOLES = (re.compile(r'\|([A-Za-z]{2,})\|'), re.compile(r'∠([A-Za-z]{2,})'))


def declared_words(records):
    """Every literal word appearing in a declared pattern."""
    out = set()
    for r in records:
        if r.kind == 'notation':
            out.update(re.findall(r'[A-Za-z]{2,}', r.fields.get('pattern', '')))
    return out


def check_run_together(report, thm, words):
    """Where a pattern puts two holes side by side, as distance does in |CA|,
    the names filling them run together in the text. If they spell a declared
    word, a reader reads the word and so does anything lexing the text.

    Points are capitals throughout this corpus, which keeps |AN| clear of the
    word `an`, but that is a convention of school geometry and not a rule:
    topology and differential geometry both name points with lowercase letters,
    and set.mm's plane is ℂ, where a point would naturally be z or w. So the
    collision is checked rather than assumed away.
    """
    for s in thm.steps:
        for text in s.claim:
            for pattern in ADJACENT_HOLES:
                for run in pattern.findall(text):
                    if run in words:
                        report.say(thm.path, s.line,
                                   f'step {fmt(s.number)} writes {run!r} in a '
                                   f'notation whose holes are adjacent, and '
                                   f'{run!r} is a declared word; rename one of '
                                   f'the names so the two do not run together')


def check_capture(report, thm, claims):
    """A substitution may not capture. If the term being substituted names a
    variable bound where it lands, the step is rejected rather than the
    variable quietly renamed, because renaming would make the machine do
    something the page does not show.
    """
    for s in thm.steps:
        if not s.just or s.just.head != 'instantiate':
            continue
        m = re.search(r'\bin\s+(?:line\s+)?([\w.]+)', s.just.text)
        if not m:
            continue
        bound = set(BINDER.findall(claims.get(m.group(1), '')))
        if not bound:
            continue
        for v, value in PAIR.findall(s.just.text):
            v, value = v.strip(), value.strip()
            # Substituting a variable for itself changes nothing and cannot
            # capture. A term that merely mentions the bound name does: that
            # mention refers to an outer binding and would be swallowed.
            if value == v:
                continue
            clash = set(VARNAME.findall(value)) & bound
            if clash:
                report.say(thm.path, s.just.line,
                           f'step {fmt(s.number)} substitutes a term naming '
                           f'{", ".join(sorted(clash))}, which is bound where it '
                           f'lands; a substitution may not capture')


SENTENCES = re.compile(r'(?<=[.])\s+')
# A `let` names what it introduces first. The keyword is part of the text in
# a proof's own lines and stripped from a database record's, so it is optional
# here and the name is what matters.
LET_NAME = re.compile(r'^(?:let\s+)?([A-Za-zα-ω][₀-₉′]*)\s*(?:∈|be\b)')


def fixed_by(records, g):
    """For each notation, the names the definition introducing it fixes.

    `def:G` writes `let a ∈ ℝ` and `let n ∈ ℕ₀`, and its sentences are
    `G(0) = 1` and `G(n + 1) = G(n) + a^(n + 1)`. The hole takes 0, n + 1
    and n, so `n` is what the notation varies over; `a` appears only outside
    it and is fixed for the whole theorem. That is the difference between a
    parameter and an argument, and it is already on the page.

    What a definition introduces is what stands on the left of its defining
    sentence, and only that. Its body may mention any notation at all —
    `def:G`'s right side is a sum and a power — and those belong to whoever
    declared them. Reading every notation a definition touches would have
    `_ + _` fixing a name, and every proof in the corpus writes `+`.

    A definition using no notation of its own fixes nothing, and so does one
    whose every `let` reaches the hole.
    """
    out = {}
    for r in records:
        if r.kind != 'definition':
            continue
        said = {m.group(1) for _k, text, _l, _n in r.hypotheses
                if (m := LET_NAME.match(text.strip()))}
        if not said:
            continue
        trees = []
        for text, _no in r.conclusions:
            for sentence in SENTENCES.split(text.strip()):
                sentence = sentence.strip().rstrip('.').strip()
                try:
                    trees.append(parse(sentence, g) if sentence else None)
                except Problem:
                    continue
        # A notation with no hole takes no argument, so it fixes nothing and
        # nothing can fill it. Without this a definition whose sentence opens
        # with a bare name — `def:gcd` has one — would have `name` fixing
        # every letter it mentions, and every formula ever written is a name.
        introduced = {t.children[0].notation for t in trees
                      if t is not None and t.children and t.children[0].children}
        filled = set()
        for node in walk([t for t in trees if t is not None]):
            if node.notation not in introduced:
                continue
            for hole in node.children:
                filled |= {(node.notation, v)
                           for v in VARNAME.findall(hole.shape())}
        for notation in introduced:
            held = {v for v in said if (notation, v) not in filled}
            if held:
                out.setdefault(notation, set()).update(held)
    return out


def check_declared(report, records, fixed):
    """What a notation's target holds fixed is what its definition fixes.

    Two files say which names a notation holds fixed and neither reads the
    other. `db/items.records` says it by what the definition's `let` lines
    name and where the hole goes, which is the reading on the page;
    `db/notation.records` says it with `@a` in the target, which is what an
    elaborator builds the term from. A target fixing a name the definition
    does not is a term about something nothing declares; a definition fixing
    a name the target does not is a parameter dropped from the term.
    """
    for r in records:
        if r.kind != 'notation' or 'target' not in r.fields:
            continue
        said = set()
        for entry in targets.split_entries(r.fields['target']):
            if entry not in targets.MARKERS:
                said |= set(targets.fixes(entry))
        wanted = fixed.get(r.name, set())
        for name in sorted(said - wanted):
            report.say(r.path, r.line,
                       f'{r.name} targets @{name}, which no definition '
                       f'introducing it fixes')
        for name in sorted(wanted - said):
            report.say(r.path, r.line,
                       f'{r.name} is introduced by a definition that fixes '
                       f'{name}, which its target does not write as @{name}')


def check_fixed(report, thm, fixed, g):
    """A proof may not bind a name the notation it uses fixes.

    `G(n)` is the sum of the powers of `a`, and `a` is fixed by `def:G` for
    the whole theorem rather than shown in the notation. A proof that bound
    an `a` of its own while writing `G(n)` would be writing about the name
    it bound, and nothing downstream would say so: the term is built from
    whatever the proof holds when the notation is read, and a bound name is
    exactly what it holds. `ELABORATION.md` calls this capture, and it is a
    rule about the page rather than about the tools, which is why it is
    here.

    Refused rather than renamed, for the reason a substitution that captures
    is refused: renaming would make the machine do something the page does
    not show.
    """
    if not fixed:
        return
    bound = {}
    for s in thm.steps:
        for name in BINDER.findall(' '.join(s.claim)):
            bound.setdefault(name, (s.line, f'step {fmt(s.number)}'))
        for kind, text, _l, no, _p in s.openers:
            if kind == 'let' and (m := LET_NAME.match(text.strip())):
                bound.setdefault(m.group(1), (no, 'a fix'))
    if not bound:
        return
    for s in thm.steps:
        for sentence in SENTENCES.split(' '.join(s.claim).strip()):
            sentence = sentence.strip().rstrip('.').strip()
            try:
                tree = parse(sentence, g) if sentence else None
            except Problem:
                continue
            for node in walk([tree] if tree else []):
                clash = set(bound) & fixed.get(node.notation, set())
                for name in sorted(clash):
                    line, where = bound[name]
                    report.say(thm.path, line,
                               f'{where} binds {name}, which `{node.notation}`'
                               f' fixes; a proof may not bind a name the '
                               f'notation it uses fixes')


class Library:
    """What each item asks a citation to supply.

    Only the hypotheses that are facts. `let X be a set`, `let P be a point`
    and a function type declare a variable and are filled by the instantiation,
    which is what Metamath calls a floating hypothesis; a membership and an
    `assume` are essential and a step citing the item has to supply them.

    A record with two `then` groups, as def:S has, states each conclusion under
    the hypotheses written above it, so the groups are kept apart and a
    citation satisfies any one of them.
    """

    def __init__(self, records, theorems, g):
        self.g = g
        self.items = {r.name: r for r in records
                      if r.kind in ('definition', 'theorem')}
        self.proved = {t.name: t for t in theorems}
        self.cache = {}
        # Which notations are an existential and which a membership, taken
        # from what they target in the kernel rather than named here. A
        # metamath field may say more after the target, as "wrex, and wrex
        # under wn" does, so the target is its first word.
        self.exists, self.members = set(), set()
        self.conj, self.bicond, self.impl = set(), set(), set()
        targets = {'wrex': self.exists, 'wcel': self.members, 'wa': self.conj,
                   'wb': self.bicond, 'wi': self.impl}
        for r in records:
            if r.kind != 'notation':
                continue
            first = re.match(r'[a-z0-9-]+', r.fields.get('metamath', '').strip())
            if first and first.group(0) in targets:
                targets[first.group(0)].add(r.name)
        self.binders, self.props = binding_context(g.notations)

    def groups(self, name):
        if name not in self.cache:
            self.cache[name] = self._read(name)
        return self.cache[name]

    def _read(self, name):
        """One (hypotheses, conclusion sentences) pair per `then` group."""
        thm = self.proved.get(name)
        if thm is not None:
            sorts = sorts_in_scope(thm, self.g)
            lines = [(k, LABEL_AT_END.sub('', t[len(k):]).strip())
                     for k, t, _, _ in thm.hypotheses]
            return [(self._facts(lines, sorts),
                     self._trees(sentences(thm.conclusion), sorts))]
        item = self.items.get(name)
        if item is None:
            return None
        sorts = sorts_of_record(item)
        out = []
        for text, at in item.conclusions:
            lines = [(h[0], LABEL_AT_END.sub('', h[1]).strip())
                     for h in item.hypotheses
                     if h[0] in ('let', 'assume') and h[3] < at]
            out.append((self._facts(lines, sorts),
                        self._trees(sentences(text), sorts)))
        return out or [([], [])]

    def _trees(self, texts, sorts):
        out = []
        for text in texts:
            self.g.sorts = sorts
            try:
                out.append(parse(text, self.g))
            except Problem:
                continue
        return out

    def _facts(self, lines, sorts):
        out = []
        for kind, text in lines:
            if kind == 'let' and (KIND.match(text) or FUNCTION.match(text)):
                continue
            self.g.sorts = sorts
            try:
                out.append((text, parse(text, self.g)))
            except Problem:
                continue
        return out


def negates(a, b, wrappers):
    """True when a is b with a negation in front.

    A folded negation counts, because a record declaring `negates` makes
    "n is not odd" the same tree as "not (n is odd)". `wrappers` is the set of
    notations those records name, so no notation is known here by its text.
    """
    return (a is not None and b is not None and a.children
            and a.notation in wrappers and a.children[0].shape() == b.shape())


def check_contradiction(report, thm, g):
    """A contradiction block relates its supposition to its claim, and closes
    with a formula and that formula's negation.

    METHODS.md specifies the two shapes: the supposition is the claim negated,
    which is reductio, or the claim is the supposition negated, which proves a
    negation directly. No formula is its own double negation, so at most one
    holds and the expansion each needs is never in doubt. Anything else the
    method refuses, which is why this is reported rather than left to fail
    later with nothing to point at.
    """
    sorts_in_scope(thm, g)
    wrappers = {n.folds for n in g.notations if n.folds}
    defined = definitions_in_scope(thm, g)
    thm_sorts = sorts_in_scope(thm, g)

    def read(text):
        g.sorts = thm_sorts
        try:
            return expand(parse(text, g), defined)
        except Problem:
            return None
    for step in thm.steps:
        if not step.just or step.just.head != 'contradiction':
            continue
        opener = next(((t, k) for k, t, _, _, _ in step.openers
                       if k == 'suppose'), None)
        if opener is None:
            continue                  # already reported as a missing suppose
        supposed = read(LABEL_AT_END.sub('', opener[0][len(opener[1]):]).strip())
        claimed = read(' '.join(step.claim))
        if supposed is None or claimed is None:
            continue                  # already reported as unreadable
        if not (negates(supposed, claimed, wrappers)
                or negates(claimed, supposed, wrappers)):
            report.say(thm.path, step.line,
                       f'step {fmt(step.number)} supposes something that is '
                       f'neither its claim negated nor the thing its claim '
                       f'negates, so neither expansion of `contradiction` '
                       f'applies')

        inside = [s for s in thm.steps
                  if len(s.number) > len(step.number)
                  and s.number[:len(step.number)] == step.number]
        if not inside:
            continue
        last = sentences(' '.join(inside[-1].claim))
        pair = [read(s) for s in last] if len(last) == 2 else []
        if len(pair) != 2 or not (negates(pair[0], pair[1], wrappers)
                                  or negates(pair[1], pair[0], wrappers)):
            report.say(thm.path, inside[-1].line,
                       f'step {fmt(inside[-1].number)} ends a contradiction '
                       f'block and does not state a formula and that formula '
                       f'negated')


def supply(patterns, facts, binding, variables, library,
           sites=frozenset(), reuse=False):
    """Every hypothesis is stated by one of the facts.

    A hypothesis that is a "there is" may instead be stated by a fact giving
    its body with some value in place of the bound variable, which is the move
    SYNTAX.md describes for exhibit: the cited line determines the value and
    the text never writes it. `there is s ∈ S`, which says only that S has a
    member, is stated by any fact putting something in S.
    """
    if not patterns:
        return binding
    first, rest = patterns[0], patterns[1:]
    # A property already bound stands for a formula, so what it asks of the
    # facts is that formula rather than the application. Filling it in first is
    # what lets the rules below see it: `P(a)` may turn out to be a "there is",
    # and then a fact giving an instance of it supplies it.
    if (first.notation in library.props and len(first.children) == 2
            and first.children[0].notation == 'name'):
        stands = binding.get(first.children[0].text)
        if stands is not None and stands.notation == PROPERTY:
            arg = first.children[1]
            if arg.notation == 'name' and arg.text in binding:
                arg = binding[arg.text]
            first = substitute(stands.children[0], {stands.text: arg})
    forms = [(first, variables)]
    if first.notation in library.exists and len(first.children) > 2:
        # A "there is" pattern holds its body last and names its variables
        # before it, one name and one domain at a time, so the two-variable
        # form is read the same way as the one-variable form.
        body = first.children[-1]
        named = {c.text for c in first.children[:-1] if c.notation == 'name'}
        forms.append((body, variables | named))
    for i, fact in enumerate(facts):
        for form, seen in forms:
            found = match(form, fact, binding, seen, library.props, sites)
            if (found is None and form is first
                    and first.notation in library.exists
                    and len(first.children) == 2
                    and fact.notation in library.members
                    and len(fact.children) == 2):
                found = match(first.children[1], fact.children[1],
                              binding, variables)
            if found is None:
                continue
            # A fact is used once when nothing has pinned the binding yet, or
            # a variable free in two hypotheses binds to whatever made the
            # first of them match and the second is then satisfied by the same
            # line. Where the claim has already pinned it, as in the conclusion
            # check, one line may legitimately answer two requirements: a
            # hypothesis and what an unfolding asks for are often the same
            # fact.
            # A hypothesis whose every variable the binding already fixed is
            # a closed claim, and what goes wrong above cannot: nothing is
            # left for the line to bind. `card-disjoint-union` at m := 2^k
            # and n := 2^k asks `2^k ∈ ℕ₀` twice, and one line says it.
            pinned = all(n.text in binding for n in walk([first])
                         if n.notation == 'name' and n.text in variables)
            rest_facts = (facts if reuse or pinned
                          else facts[:i] + facts[i + 1:])
            done = supply(rest, rest_facts, found, variables, library, sites,
                          reuse)
            if done is not None:
                return done
    return None


def statements_in_scope(thm):
    """Every line a citation may name, by the reference that names it."""
    out = {fmt(s.number): ' '.join(s.claim) for s in thm.steps}
    lines = [(k, t, lab) for k, t, lab, _ in thm.hypotheses]
    lines += [(k, t, lab) for s in thm.steps for k, t, lab, _, _ in s.openers]
    for kind, text, label in lines:
        if label:
            out[label] = LABEL_AT_END.sub('', text[len(kind):]).strip()
    return out


def citation_parts(step, just, scope, library, sorts, defined):
    """What a citation supplies, what it claims, and what it says its
    variables stand for.

    A defined name and the term it names are one formula, so all three are
    expanded: the facts, the claim, and the written instantiation alike.
    """
    g = library.g
    supplied = []
    for ref in just.refs:
        if ref in scope:
            supplied += sentences(scope[ref])
    supplied += [fact for fact, _, _ in step.requires]

    def read(text):
        g.sorts = sorts
        try:
            return expand(parse(text, g), defined)
        except Problem:
            return None

    facts = [x for x in map(read, supplied) if x is not None]
    claims = [x for x in map(read, sentences(' '.join(step.claim)))
              if x is not None]
    seed = {}
    for name, value in instantiation(just.text):
        got = read(value)
        if got is not None:
            seed[name] = got
    return facts, claims, seed


def conjuncts(node, library):
    """A conjunction taken apart. A claim may take one part of what it gets,
    and a fact may supply one part of what is asked, because a line is a
    conjunction at kernel level either way and the projection lives in the
    method's expansion.
    """
    if node.notation in library.conj and len(node.children) == 2:
        return (conjuncts(node.children[0], library)
                + conjuncts(node.children[1], library))
    return [node]


def readings(node, library):
    """(what a step may claim, what a fact must state first), for one sentence
    of an item's conclusion.

    SYNTAX.md gives the moves: a sentence may be claimed as it stands; where it
    is "A ↔ B" and a fact states A the step may claim B, and the other way
    round; where it is "if A then B" and a fact states A the step may claim B.
    """
    out = [(node, [])]
    if len(node.children) == 2:
        left, right = node.children
        if node.notation in library.bicond:
            out += [(right, [left]), (left, [right])]
        elif node.notation in library.impl:
            out.append((right, [left]))
    return out


def take(claims, candidates, binding, used, need, given, variables, library,
         sites):
    """Every sentence of the claim takes a reading of the conclusion, and what
    those readings ask for is then supplied by the facts.

    It backtracks, because a sentence can fit a reading whose requirement the
    step does not meet while another reading's it does.
    """
    if not claims:
        return supply(need + used, given, binding, variables, library,
                      sites, reuse=True) is not None
    for cand, first in candidates:
        # What a property stands for is decided inside the braces, so a
        # requirement holding them is matched before the claim that uses it.
        start = binding
        if any(id(x) in sites for x in walk(first)):
            start = supply(first, given, binding, variables, library, sites)
            if start is None:
                continue
        found = match(cand, claims[0], start, variables, library.props, sites)
        if found is None:
            continue
        seen = {u.shape() for u in used}
        more = [f for f in first if f.shape() not in seen]
        if take(claims[1:], candidates, found, used + more, need, given,
                variables, library, sites):
            return True
    return False


def walk(nodes):
    for node in nodes:
        yield node
        yield from walk(node.children)


def check_conclusion(report, thm, library):
    """A citation's claim is what the item concludes, under the binding its
    hypotheses fixed.
    """
    g = library.g
    sorts = sorts_in_scope(thm, g)
    defined = definitions_in_scope(thm, g)
    scope = statements_in_scope(thm)

    for step in thm.steps:
        just = step.just
        if not just or not just.head.startswith(('def:', 'thm:')):
            continue
        groups = library.groups(just.head.split(':', 1)[1])
        if groups is None:
            continue
        facts, claims, seed = citation_parts(step, just, scope, library,
                                             sorts, defined)
        if not claims:
            continue
        if not concludes(groups, claims, facts, seed, library):
            report.say(thm.path, just.line,
                       f'step {fmt(step.number)} claims something that '
                       f'{just.head} does not conclude')


def concludes(groups, claims, facts, seed, library):
    """Whether one group of an item's conclusions covers what is claimed."""
    for want, gives in groups:
        candidates, sites = [], set()
        for concl in gives:
            binding_sites(concl, library.binders, library.props, (), sites)
            for target, extra in readings(concl, library):
                first = [x for e in extra for x in conjuncts(e, library)]
                candidates += [(c, first) for c in conjuncts(target, library)]
        need = [x for _, t in want for x in conjuncts(t, library)]
        for w in want:
            binding_sites(w[1], library.binders, library.props, (), sites)
        trees = gives + [t for _, t in want]
        variables = set().union(*(names(t) for t in trees)) if trees else set()
        if take(claims, candidates, dict(seed), [], need, facts,
                variables, library, sites):
            return True
    return False


def check_requires(report, thm, library):
    """A requires line needs what the item it cites concludes.

    A step's citation is matched this way already. A requires line carries the
    same kind of pointer to the same kind of item, and was checked only for
    resolving, so an item that did not cover the fact went unnoticed.
    """
    g = library.g
    sorts = sorts_in_scope(thm, g)
    defined = definitions_in_scope(thm, g)
    scope = statements_in_scope(thm)

    def read(text):
        g.sorts = sorts
        try:
            return expand(parse(text, g), defined)
        except Problem:
            return None

    for step in thm.steps:
        for fact, how, no in step.requires:
            named = re.match(rf'^(def|thm):({NAME})', how)
            if not named:
                continue
            groups = library.groups(named.group(2))
            if groups is None:
                continue
            claims = [x for x in map(read, sentences(fact)) if x is not None]
            if not claims:
                continue
            refs, _bad = requires_refs(how)
            supplied = []
            for ref in refs:
                if ref in scope:
                    supplied += sentences(scope[ref])
            # A requires line may not cite another, but the facts its
            # siblings state are established for the same step and are what
            # a dull fact its own citation asks for is written as.
            supplied += [other for other, _, _ in step.requires
                         if other != fact]
            facts = [x for x in map(read, supplied) if x is not None]
            seed = {}
            for name, value in instantiation(how):
                got = read(value)
                if got is not None:
                    seed[name] = got
            if concludes(groups, claims, facts, seed, library):
                continue
            if all(derives(c, groups, facts, library) for c in claims):
                continue
            report.say(thm.path, no,
                       f'the requires line of step {fmt(step.number)} '
                       f'needs something that {named.group(0)} does not '
                       f'conclude')


def derives(claim, groups, facts, library, depth=5):
    """The fact follows from the cited item applied as often as it takes.

    A closure line names a principle, not one use of it: `2k² + 2k ∈ ℤ` cites
    `thm:int-closure` once where the kernel applies it three times, and a
    reader wants the one line. So the item's own conclusions are matched
    against the claim and against whatever they then ask for, and nothing
    else is allowed in.
    """
    if depth <= 0:
        return False
    if any(f.shape() == claim.shape() for f in facts):
        return True
    for want, gives in groups:
        trees = gives + [t for _, t in want]
        variables = set().union(*(names(t) for t in trees)) if trees else set()
        for concl in gives:
            binding = match(concl, claim, {}, variables, library.props,
                            frozenset())
            if binding is None:
                continue
            if all(derives(substitute(t, binding), groups, facts, library,
                           depth - 1) for _, t in want):
                return True
    return False


def check_hypotheses(report, thm, library):
    """A citation supplies the hypotheses of what it cites.

    They come from the lines named in `from` and from the `requires` lines,
    each of which states one fact. A cited line supplies every sentence of its
    claim, because a claim of several sentences is their conjunction.

    The item is read as a pattern and the facts are ground, so a citation that
    writes no instantiation is checked the same way as one that does: 37 of the
    corpus's 106 write none and a reader still sees the match. Where an
    instantiation is written it seeds the binding, which makes it checked
    rather than taken on trust.
    """
    g = library.g
    sorts = sorts_in_scope(thm, g)
    defined = definitions_in_scope(thm, g)
    scope = statements_in_scope(thm)

    for step in thm.steps:
        just = step.just
        if not just or not just.head.startswith(('def:', 'thm:')):
            continue
        groups = library.groups(just.head.split(':', 1)[1])
        if groups is None:
            continue                      # a pointer that resolves to nothing
        facts, _, seed = citation_parts(step, just, scope, library, sorts,
                                        defined)

        missing = None
        for want, _ in groups:
            if not want:
                missing = None
                break
            variables = set().union(*(names(t) for _, t in want))
            if supply([t for _, t in want], facts,
                      dict(seed), variables, library, frozenset()) is not None:
                missing = None
                break
            missing = [t for t, _ in want]
        if missing is not None:
            report.say(thm.path, just.line,
                       f'step {fmt(step.number)} cites {just.head}, which asks '
                       f'for {"; ".join(missing)}, and what it cites does not '
                       f'supply them')


def sentences(text):
    return [s.strip().rstrip('.').strip()
            for s in SENTENCES.split(text.strip()) if s.strip()]


def check_statements(report, records, g):
    """Every statement in the database parses, and parses one way.

    An item's statement is a formula in the same language as a claim, and the
    elaborator matches one against the other, so a statement that does not read
    is a defect wherever it is written. An item proved in this corpus keeps its
    statement at the head of its proof file and has none here.
    """
    for r in records:
        if r.kind not in ('definition', 'theorem'):
            continue
        g.sorts = sorts_of_record(r)
        for kind, text, _, no in r.hypotheses:
            if kind != 'let':
                continue
            said = introduction_problem(LABEL_AT_END.sub('', text).strip())
            if said:
                report.say(r.path, no, f'{r.kind} {r.name}: {said}')
        places = [(text, no) for kind, text, _, no in r.hypotheses
                  if kind == 'assume']
        places += list(r.conclusions)
        for text, no in places:
            for sentence in SENTENCES.split(LABEL_AT_END.sub('', text).strip()):
                sentence = sentence.strip().rstrip('.').strip()
                if not sentence:
                    continue
                try:
                    parse(sentence, g)
                except Problem as p:
                    report.say(r.path, no, f'{r.kind} {r.name}: {p.message}')


def check_symbols(report, records):
    """A definition that introduces a symbol says which, and is alone in it.

    Most definitions name a word for something the library already has and
    introduce nothing: `def:even` is divisibility by two, `def:irrational` is
    membership of the reals minus the rationals. One that introduces a symbol
    is the case decision 12 of `GOALS.md` is about, wanting a definitional
    axiom "syntactically checked to introduce one new symbol and be
    eliminable". It says so with a `symbol` field naming the token, and a
    `defines` field giving the term the token stands for.

    What is checked here is what the corpus knows about itself: that the two
    fields come together, that the token is one word, that no two definitions
    claim the same token, and that some notation actually reaches it. Whether
    the token is already a label of the library, and whether the term parses
    and closes over its own variables, wants the library — which this checker
    does not read — and is checked where the library is.
    """
    claimed = {}
    for r in records:
        if r.kind != 'definition':
            continue
        token = r.fields.get('symbol', '').strip()
        body = r.fields.get('defines', '').strip()
        if token and not body:
            report.say(r.path, r.line,
                       f'definition {r.name}: introduces {token!r} and says '
                       f'nothing it stands for')
        if body and not token:
            report.say(r.path, r.line,
                       f'definition {r.name}: defines a term and names no '
                       f'symbol for it')
        if not token:
            continue
        if len(token.split()) != 1:
            report.say(r.path, r.line,
                       f'definition {r.name}: {token!r} is not one token')
            continue
        if token in claimed:
            report.say(r.path, r.line,
                       f'definition {r.name}: {token!r} is already introduced '
                       f'by definition {claimed[token]}')
            continue
        claimed[token] = r.name
    # A symbol nothing reaches is a symbol the corpus cannot write. The
    # constant a definition introduces is `c` and the token, by the naming
    # set.mm uses for every other one.
    reached = set()
    for r in records:
        if r.kind != 'notation':
            continue
        reached.update(r.fields.get('target', '').split())
    for token, name in claimed.items():
        if f'c{token}' not in reached:
            report.say('db/items.records', 0,
                       f'definition {name}: nothing writes c{token}, so the '
                       f'symbol it introduces cannot be reached')


def check_formulas(report, thm, g):
    """Every formula on the page parses, and parses one way.

    A claim, an `assume` or `suppose` line, the fact of a `requires` line and
    the theorem's statement are all formulas, read from the declared notations.
    One that does not parse is a defect in the text or a notation nobody
    declared. One that parses two ways is worse, because the reader and the
    kernel could take it differently and nothing downstream would notice, so
    the parser refuses it rather than choosing.

    This is the pass that says so, and it reaches every one of them. That is
    what lets the passes which merely gather — sorts, the names a `fix`
    binds, the trees an item states — skip a formula they cannot read and
    carry on: it has been reported here, once, with the line it is on. A
    pass that gathered and also complained would say it twice; one that
    stopped would hide the rest of what it was looking for behind the first
    defect.
    """
    sorts_in_scope(thm, g)
    places = [(s.line, f'step {fmt(s.number)}', ' '.join(s.claim))
              for s in thm.steps]
    places += [(no, f'the requires line of step {fmt(s.number)}', fact)
               for s in thm.steps for fact, _, no in s.requires]
    lines = [(k, t, n) for k, t, _, n in thm.hypotheses]
    lines += [(k, t, n) for s in thm.steps for k, t, _, n, _ in s.openers]
    places += [(n, f'the `{k}` line', LABEL_AT_END.sub('', t[len(k):]).strip())
               for k, t, n in lines if k in ('assume', 'suppose')]
    places.append((thm.line, f'the statement of {thm.name}', thm.conclusion))
    for line, what, text in places:
        for sentence in SENTENCES.split(text.strip()):
            sentence = sentence.strip().rstrip('.').strip()
            if not sentence:
                continue
            try:
                parse(sentence, g)
            except Problem as p:
                report.say(thm.path, line, f'{what}: {p.message}')


def check_sorts(report, thm):
    """Every variable's sort is on the page, so the parser never infers one.

    A `let` line gives it, and so does the claim of the `obtain` step that
    introduces a name. Without that rule a parser would have to chase the
    cited item's conclusion to learn a sort, and sorts are what disambiguate
    a notation, so two implementations chasing differently would parse the
    same formula differently.
    """
    for s in thm.steps:
        if not s.just or s.just.head != 'obtain':
            continue
        m = OBTAIN_NAMES.match(s.just.text)
        if not m:
            continue
        claim = ' '.join(s.claim)
        for v in (x.strip() for x in m.group(1).split(',')):
            if not v:
                continue
            n = re.escape(v)
            stated = (re.search(rf'(?<![A-Za-z]){n}\s*∈', claim)
                      or re.search(rf'(?<![A-Za-z]){n}\s+is a (set|point)', claim)
                      or re.search(rf'(?<![A-Za-z]){n}\s*:', claim))
            if not stated:
                report.say(thm.path, s.line,
                           f'step {fmt(s.number)} obtains {v} without stating its '
                           f'sort; the claim of an obtain states the membership '
                           f'of each name it introduces, so no sort is inferred')


INTRODUCTIONS = (
    ('a membership',            re.compile(r'^\S+\s*∈\s*\S')),
    ('an arbitrary set',        re.compile(r'^\S+\s+be a set$')),
    ('an arbitrary point',      re.compile(r'^\S+\s+be a point$')),
    ('a function',              re.compile(r'^\S+\s*:\s*.+→.+$')),
    ('a property',              re.compile(r'^\S+\s+be a property of the '
                                           r'elements of\s+\S+$')),
)


def check_readings(report, thm):
    """A define carries a reading, and a note belongs to a block.

    A define names an object and asserts nothing, so the acceptance test has
    nothing to check about it and a reader can meet a construction with no
    idea why it is there. The reading is the one line saying what the name
    means in words. Nothing can judge the words, but their absence is the
    commonest way for the device to be forgotten, so that much is required.
    """
    for _, _, label, no in thm.defines:
        if label not in thm.readings:
            report.say(thm.path, no,
                       f'define {label} carries no `reads` line saying what '
                       f'the name means')
    for step in thm.steps:
        if step.note and (not step.just or step.just.head not in BLOCK_HEADS):
            report.say(thm.path, step.note[1],
                       f'step {fmt(step.number)} carries a note and opens no '
                       f'block; a note says what a block is doing')


def introduction_problem(body):
    """What is wrong with a `let` body, or None. Used for a proof's lines and
    for an item's alike, since an item states its hypotheses the same way.
    """
    if not any(p.match(body) for _, p in INTRODUCTIONS):
        return (f'`let {body[:40]}` is none of the five introductions: '
                f'{", ".join(n for n, _ in INTRODUCTIONS)}')
    # A function's codomain is a set. A sort is a label for what kind of thing
    # a name is, and there is no set of formulas to map into: writing one there
    # says a property is a function, which it is not.
    arrow = re.match(r'^\S+\s*:\s*.+→\s*(\S+)$', body)
    if arrow and arrow.group(1) in SORT_NAMES:
        return (f'`let {body[:40]}` sends a function into {arrow.group(1)!r}, '
                f'which is a sort and not a set; a property is introduced '
                f'with `be a property of the elements of`')
    return None


def check_introductions(report, thm):
    """A `let` line carries an introduction, not a formula. It names something
    and says what it is, asserting nothing, and there are exactly four forms.
    `assume` takes a formula, because it does assert.
    """
    lines = [(k, t, n) for k, t, _, n in thm.hypotheses]
    for s in thm.steps:
        lines += [(k, t, n) for k, t, _, n, _ in s.openers]
    for kind, text, no in lines:
        if kind != 'let':
            continue
        body = re.sub(r'^\s*let\s+', '', text)
        body = re.sub(r'\s*\([A-Z]+[0-9]*\)\s*$', '', body).strip()
        said = introduction_problem(body)
        if said:
            report.say(thm.path, no, said)


def check_last_step(report, thm):
    if not thm.steps:
        report.say(thm.path, thm.line, f'theorem {thm.name} has no steps')


# -------------------------------------------------------------------- main

def main(root):
    root = Path(root)
    report = Report()

    db_files = sorted((root / 'db').glob('*.records'))
    proof_files = sorted((root / 'proof').glob('*.proof'))
    if not db_files or not proof_files:
        print(f'no corpus under {root}', file=sys.stderr)
        return 2

    records, texts = [], {}
    for path in db_files + proof_files:
        rel = str(path.relative_to(root))
        try:
            texts[rel] = check_encoding(rel, path.read_bytes())
        except Problem as p:
            report.problems.append(p)

    for path in db_files:
        rel = str(path.relative_to(root))
        if rel not in texts:
            continue
        try:
            records.extend(parse_database(rel, texts[rel]))
        except Problem as p:
            report.problems.append(p)

    items = {r.name: r for r in records if r.kind in ('definition', 'theorem')}
    methods = {r.name: r for r in records if r.kind == 'method'}
    notation = [r for r in records if r.kind == 'notation']
    allowed = set()
    for r in notation:
        for value in r.fields.values():
            allowed.update(value)
    allowed.update(IDENTIFIER_CHARACTERS)

    check_database(report, records)
    check_notation(report, records)
    words = declared_words(records)

    theorems = []
    for path in proof_files:
        rel = str(path.relative_to(root))
        if rel not in texts:
            continue
        check_characters(report, rel, texts[rel], allowed)
        try:
            found = parse_proof(rel, texts[rel])
        except Problem as p:
            report.problems.append(p)
            continue
        theorems.extend(found)

    grammar = Grammar.load(records)
    check_statements(report, records, grammar)
    check_symbols(report, records)

    library = Library(records, theorems, grammar)
    fixes = fixed_by(records, grammar)
    check_declared(report, records, fixes)

    proved = {}
    for thm in theorems:
        check_formulas(report, thm, grammar)
        check_contradiction(report, thm, grammar)
        check_hypotheses(report, thm, library)
        check_conclusion(report, thm, library)
        check_requires(report, thm, library)
        check_last_step(report, thm)
        check_readings(report, thm)
        check_introductions(report, thm)
        check_sorts(report, thm)
        check_capture(report, thm, claims_of(thm))
        check_fixed(report, thm, fixes, grammar)
        check_run_together(report, thm, words)
        check_numbering(report, thm)
        check_blocks(report, thm, methods)
        for step in thm.steps:
            if step.just:
                check_justification_form(report, thm.path, step.just)
                check_chain(report, thm, step)
        check_citations(report, thm, items, methods, notation)
        proved.setdefault(thm.name, thm)

    for name, item in sorted(items.items()):
        where = item.fields.get('proved-in')
        if where and name not in proved:
            report.say(item.path, item.line,
                       f'{name} says it is proved in {where}, and no theorem there '
                       f'has that name')
    for thm in theorems:
        if thm.name not in items:
            report.say(thm.path, thm.line,
                       f'theorem {thm.name} is proved here and is in no record of '
                       f'db/items.records')

    for p in sorted(report.problems, key=lambda p: (p.path, p.line)):
        print(p)

    print()
    print(f'{len(theorems)} theorems, {sum(len(t.steps) for t in theorems)} steps, '
          f'{len(items)} items, {len(methods)} methods')
    print(f'{len(report.problems)} problem(s)')
    by_method = {}
    for _, _, method, _ in report.trusted:
        by_method[method] = by_method.get(method, 0) + 1
    total = sum(by_method.values())
    print(f'{total} step(s) accepted without checking, resting on a closure method:')
    for method in CLOSURE:
        if method in by_method:
            print(f'    {by_method[method]:4}  {method}')
    return 1 if report.problems else 0


if __name__ == '__main__':
    here = Path(__file__).resolve().parent.parent
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else here))
