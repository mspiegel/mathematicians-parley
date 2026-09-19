#!/usr/bin/env python3
"""Check the corpus against GRAMMAR.md.

Reports the grammar, the numbering, block structure, pointer resolution, the
scope of every citation, calculation chains, and that every formula on the page
parses one way. It does not check that a claim follows from what it cites; that
needs the elaborator.

Usage:  tools/check.py [root]
Exits non-zero when anything is reported.
"""
import re
import sys
import unicodedata
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from parse import (                                       # noqa: E402
    HEADS, LABEL, NAME, NUMBER, REF, PART_MARKERS, BLOCK_HEADS,
    Problem, check_encoding, fmt, parse_database, parse_proof, read_lines,
)
from formula import Grammar, parse                        # noqa: E402
from sorts import LABEL as LABEL_AT_END, sorts_in_scope   # noqa: E402

# The productions of GRAMMAR.md, one per justification form.
INST = r'(?:[^\s,]+\s*:=\s*.+?)(?:,\s*[^\s,]+\s*:=\s*.+?)*'
FROM = rf'from\s+{REF}(?:\s*,\s*{REF})*'
PRODUCTIONS = {
    'citation':      rf'^(?:def|thm):{NAME}(?:\s+{INST})?(?:,\s*{FROM})?$',
    'obtain-item':   rf'^obtain\s+\S+(?:\s*,\s*\S+)*:\s*(?:def|thm):{NAME}'
                     rf'(?:\s+{INST})?,\s*{FROM}$',
    'obtain-line':   rf'^obtain\s+\S+\s+from\s+line\s+{NUMBER}$',
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
    it there. Steps inside a closed block are not visible outside it."""
    if len(cited) > len(here):
        return False
    return cited[:-1] == here[:len(cited) - 1] and cited[-1] < here[len(cited) - 1]


def labels_in_scope(thm, step):
    """Hypothesis labels hold throughout a proof. A label declared by a block
    holds inside that block only. When the block has parts, a label declared by
    one part holds in that part alone, so one case of a case analysis cannot
    cite the assumption of another."""
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
        for kind, text, lab, no, part in other.openers:
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
                       f'record of db/notation.db')
            return


def check_database(report, records):
    seen = {}
    for r in records:
        key = (r.kind if r.kind in ('notation', 'method') else 'item', r.name)
        if key in seen:
            report.say(r.path, r.line,
                       f'{r.kind} {r.name} is already defined at line {seen[key]}')
        seen[key] = r.line
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
            if 'proved-in' not in r.fields and not r.conclusions and 'open' not in r.fields:
                report.say(r.path, r.line, f'{r.name} has no `then` line')
        if r.kind == 'method' and 'parts' in r.fields:
            for part in re.split(r',\s*', r.fields['parts']):
                word = part.strip().split()[0] if part.strip() else ''
                if word and word not in PART_MARKERS:
                    report.say(r.path, r.line,
                               f'method {r.name} declares part {word!r}, which is '
                               f'not a part marker')


TERM_SORTS = {'number', 'set', 'point', 'any'}


def check_notation(report, records):
    """A notation record declares a pattern, the sort of each hole, and what it
    yields. Two things follow mechanically and are checked here."""
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
    owners = {s.number: s for s in thm.steps}
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
    one is carrying a justification that belongs in a step."""
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
                       f'{just.head} is in no record of db/methods.db')
        for fact, text, no in step.requires:
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
    collision is checked rather than assumed away."""
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
    something the page does not show."""
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


def check_formulas(report, thm, g):
    """Every formula on the page parses, and parses one way.

    A claim, an `assume` or `suppose` line, the fact of a `requires` line and
    the theorem's statement are all formulas, read from the declared notations.
    One that does not parse is a defect in the text or a notation nobody
    declared. One that parses two ways is worse, because the reader and the
    kernel could take it differently and nothing downstream would notice, so
    the parser refuses it rather than choosing."""
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
    same formula differently."""
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
)


def check_introductions(report, thm):
    """A `let` line carries an introduction, not a formula. It names something
    and says what it is, asserting nothing, and there are exactly four forms.
    `assume` takes a formula, because it does assert."""
    lines = [(k, t, n) for k, t, _, n in thm.hypotheses]
    for s in thm.steps:
        lines += [(k, t, n) for k, t, _, n, _ in s.openers]
    for kind, text, no in lines:
        if kind != 'let':
            continue
        body = re.sub(r'^\s*let\s+', '', text)
        body = re.sub(r'\s*\([A-Z]+[0-9]*\)\s*$', '', body).strip()
        if not any(p.match(body) for _, p in INTRODUCTIONS):
            report.say(thm.path, no,
                       f'`let {body[:40]}` is none of the four introductions: '
                       f'{", ".join(n for n, _ in INTRODUCTIONS)}')


def check_last_step(report, thm):
    if not thm.steps:
        report.say(thm.path, thm.line, f'theorem {thm.name} has no steps')


# -------------------------------------------------------------------- main

def main(root):
    root = Path(root)
    report = Report()

    db_files = sorted((root / 'db').glob('*.db'))
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

    proved = {}
    for thm in theorems:
        check_formulas(report, thm, grammar)
        check_last_step(report, thm)
        check_introductions(report, thm)
        check_sorts(report, thm)
        check_capture(report, thm, claims_of(thm))
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
                       f'db/items.db')

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
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent))
