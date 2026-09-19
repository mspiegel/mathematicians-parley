"""Parse the database files and the proof skeletons described by GRAMMAR.md.

A claim is an opaque run of text. Nothing here looks inside a formula.
"""
import re
import unicodedata
from dataclasses import dataclass, field

NAME = r'[A-Za-z][A-Za-z0-9-]*'
LABEL = r'[A-Z]+[0-9]*'
NUMBER = r'\d+(?:\.\d+)*'
REF = rf'(?:{NUMBER}|{LABEL})'

HEADS = ('def:', 'thm:', 'obtain', 'exhibit', 'substitute', 'instantiate',
         'algebra', 'arithmetic', 'inequalities', 'join', 'contradiction',
         'fix', 'induction', 'cases', 'calculation')
PART_MARKERS = ('base', 'step', 'case')
BLOCK_HEADS = ('contradiction', 'fix', 'induction', 'cases', 'calculation')


class Problem(Exception):
    """A defect found while reading. Carries where it was found."""

    def __init__(self, path, line, message):
        super().__init__(message)
        self.path, self.line, self.message = path, line, message

    def __str__(self):
        return f'{self.path}:{self.line}  {self.message}'


@dataclass
class Line:
    """One logical line: a physical line plus any continuations of it."""
    path: str
    no: int
    text: str
    indent: int


def read_lines(path, text):
    """Physical lines, comments and blanks dropped, joined by the continuation
    rule: a line continues onto the next when it ends with a comma."""
    out, pending = [], None
    for no, raw in enumerate(text.split('\n'), 1):
        if not raw.strip() or raw.lstrip().startswith('#'):
            if pending:
                out.append(pending)
                pending = None
            continue
        stripped = raw.strip()
        indent = len(raw) - len(raw.lstrip())
        if pending is not None:
            pending.text += ' ' + stripped
            if not stripped.endswith(','):
                out.append(pending)
                pending = None
            continue
        line = Line(path, no, stripped, indent)
        if stripped.endswith(','):
            pending = line
        else:
            out.append(line)
    if pending:
        out.append(pending)
    return out


# --------------------------------------------------------------- database

@dataclass
class Record:
    kind: str
    name: str
    fields: dict = field(default_factory=dict)
    hypotheses: list = field(default_factory=list)
    conclusions: list = field(default_factory=list)
    line: int = 0
    path: str = ''


RECORD_KINDS = ('notation', 'method', 'definition', 'theorem', 'precedence')


def parse_database(path, text):
    """Records of db/*.db. A record begins at column 0; its fields are
    indented. `let`, `assume` and `then` lines carry an item's statement."""
    records, cur = [], None
    # A field sits at the record's field indent. Anything indented further
    # continues the field above it, which is how a long `note` is wrapped.
    # Without this every wrapped line became a field named after its first
    # word, and a record ended up with fields called `are` and `them.`.
    field_indent, last = None, None
    for line in read_lines(path, text):
        head = line.text.split(None, 1)
        if line.indent == 0:
            if head[0] not in RECORD_KINDS:
                raise Problem(path, line.no, f'unknown record kind {head[0]!r}')
            if len(head) < 2 or not re.fullmatch(NAME, head[1].strip()):
                raise Problem(path, line.no, 'record has no well-formed name')
            cur = Record(head[0], head[1].strip(), line=line.no, path=path)
            records.append(cur)
            field_indent, last = None, None
            continue
        if cur is None:
            raise Problem(path, line.no, 'field outside any record')
        if field_indent is None:
            field_indent = line.indent
        elif line.indent > field_indent:
            if last is None:
                raise Problem(path, line.no, 'continuation before any field')
            what, key = last
            if what == 'field':
                cur.fields[key] = (cur.fields.get(key, '') + ' ' + line.text).strip()
            elif what == 'hypothesis':
                k, v, lab, no = cur.hypotheses[-1]
                cur.hypotheses[-1] = (k, (v + ' ' + line.text).strip(), lab, no)
            else:
                v, no = cur.conclusions[-1]
                cur.conclusions[-1] = ((v + ' ' + line.text).strip(), no)
            continue
        key = head[0]
        value = head[1].strip() if len(head) > 1 else ''
        if key in ('let', 'assume'):
            last = ('hypothesis', key)
            m = re.search(rf'\(({LABEL})\)$', line.text)
            cur.hypotheses.append((key, value, m.group(1) if m else None, line.no))
        elif key == 'then':
            last = ('conclusion', key)
            cur.conclusions.append((value, line.no))
        else:
            last = ('field', key)
            cur.fields[key] = (cur.fields[key] + ' ' + value
                               if key in cur.fields else value)
    return records


# ------------------------------------------------------------------ proofs

@dataclass
class Justification:
    head: str            # 'def:sqrt', 'thm:foo', or a method name
    text: str
    line: int
    refs: list = field(default_factory=list)      # everything cited, in order
    target: str = None                            # instantiate's `in ...`
    instantiations: list = field(default_factory=list)
    chain: list = field(default_factory=list)     # (text, line) of a calculation
    bad_ref: str = None       # a `from` entry that is neither a line nor a label


@dataclass
class Step:
    number: tuple
    claim: list
    just: Justification
    requires: list = field(default_factory=list)
    parts: list = field(default_factory=list)     # part markers of the block it owns
    openers: list = field(default_factory=list)   # (kind, text, label, line, part)
    line: int = 0
    part: int = None          # which part of its parent's block this step sits in
    note: tuple = None        # (text, line) saying what the block it opens does


@dataclass
class Theorem:
    name: str
    hypotheses: list = field(default_factory=list)   # (kind, text, label, line)
    conclusion: str = ''
    defines: list = field(default_factory=list)
    readings: dict = field(default_factory=dict)   # define label -> (text, line)
    steps: list = field(default_factory=list)
    line: int = 0
    path: str = ''


def _refs(text):
    """References named by a justification, read from their syntactic position
    and never by scanning for digits."""
    out = []
    m = re.search(rf'\bfrom\s+line\s+({NUMBER})\b', text)
    if m:
        out.append(m.group(1))
    else:
        m = re.search(r'\bfrom\s+(.*)$', text)
        if m:
            for tok in m.group(1).split(','):
                tok = tok.strip()
                if re.fullmatch(REF, tok):
                    out.append(tok)
                elif tok:
                    return out, tok        # a `from` entry that is not a reference
    return out, None


def parse_justification(path, line):
    text = line.text
    head = next((h for h in HEADS if text.startswith(h)), None)
    if head is None:
        raise Problem(path, line.no, f'no justification head in {text[:40]!r}')
    if head in ('def:', 'thm:'):
        m = re.match(rf'(?:def|thm):{NAME}', text)
        head = m.group(0)
    j = Justification(head=head, text=text, line=line.no)
    # A malformed justification is reported by the checker, not raised here: one
    # bad line must not cost the reader every later line in the file.
    j.refs, j.bad_ref = _refs(text)
    for src in re.finditer(rf'\((?:line\s+({NUMBER})|({LABEL}))\)', text):
        j.refs.append(src.group(1) or src.group(2))
    for dest in re.finditer(rf'\binto\s+(?:line\s+({NUMBER})|({LABEL}))\b', text):
        j.refs.append(dest.group(1) or dest.group(2))
    m = re.search(rf'\bin\s+(?:line\s+({NUMBER})|(def:{NAME})|({LABEL}))\b', text)
    if m:
        j.target = m.group(1) or m.group(2) or m.group(3)
        if j.target and not j.target.startswith('def:'):
            j.refs.append(j.target)
    if head == 'join':
        for tok in text[len('join'):].split(','):
            tok = tok.strip()
            if re.fullmatch(REF, tok):
                j.refs.append(tok)
    j.instantiations = re.findall(r'([^\s,]+)\s*:=', text)
    return j


STEP_RE = re.compile(rf'^({NUMBER})\.\s+(.*)$')


def parse_proof(path, text):
    """Theorems of a .proof file. Structure comes from the step number;
    indentation is presentation and is not consulted."""
    theorems, thm, step, claim, defined = [], None, None, None, None
    # A part marker or a block opener appears before the sub-steps it governs,
    # so it is held until the next step arrives and is then attached to that
    # step's parent, which is the step that owns the block.
    pending_markers, pending_openers, part_no = [], [], {}
    by_number = {}

    def close_step():
        nonlocal step
        if step is not None and step.just is None:
            raise Problem(path, step.line,
                          f'step {fmt(step.number)} has no justification')
        step = None

    def attach(number):
        """Resolve held markers and openers against the owner of the block that
        the step numbered `number` sits in, and say which part it sits in."""
        parent = number[:-1]
        owner = by_number.get(parent)
        for marker, no in pending_markers:
            if owner is None:
                raise Problem(path, no, f'part marker {marker!r} outside any block')
            owner.parts.append((marker, no))
            part_no[parent] = part_no.get(parent, -1) + 1
        pending_markers.clear()
        current = part_no.get(parent)
        for kind, text, label, no in pending_openers:
            if owner is None:
                raise Problem(path, no, f'{kind} line outside any block')
            owner.openers.append((kind, text, label, no, current))
        pending_openers.clear()
        return current

    for line in read_lines(path, text):
        t = line.text
        # A `reads` line belongs to the define immediately above it, so what a
        # define leaves behind survives exactly one line.
        defined, just_defined = None, defined
        if t.startswith('theorem ') and line.indent == 0:
            close_step()
            name = t[len('theorem '):].strip()
            if not re.fullmatch(NAME, name):
                raise Problem(path, line.no, f'theorem name {name!r} is malformed')
            thm = Theorem(name=name, line=line.no, path=path)
            theorems.append(thm)
            pending_markers.clear()
            pending_openers.clear()
            part_no.clear()
            by_number.clear()
            continue
        if thm is None:
            raise Problem(path, line.no, 'text before any theorem header')

        m = STEP_RE.match(t)
        if m:
            close_step()
            number = tuple(int(x) for x in m.group(1).split('.'))
            part = attach(number)
            step = Step(number=number, claim=[m.group(2)], just=None,
                        line=line.no, part=part)
            thm.steps.append(step)
            by_number[number] = step
            claim = step
            continue

        head = t.split(None, 1)[0]
        if head in ('let', 'assume') and step is None:
            lab = re.search(rf'\(({LABEL})\)$', t)
            thm.hypotheses.append((head, t, lab.group(1) if lab else None, line.no))
            continue
        if head == 'then' and step is None:
            thm.conclusion = t[len('then'):].strip()
            continue
        if head == 'define':
            lab = re.search(rf'\(({LABEL})\)$', t)
            if not lab:
                raise Problem(path, line.no, 'define line carries no label')
            # A define names an object and is in scope from where it stands on.
            thm.defines.append(('define', t, lab.group(1), line.no))
            defined = thm.defines[-1]
            continue
        if head == 'reads':
            if just_defined is None:
                raise Problem(path, line.no,
                              'reads line that does not follow a define')
            thm.readings[just_defined[2]] = (t[len('reads'):].strip(), line.no)
            continue
        if head == 'note':
            if step is None or not step.just:
                raise Problem(path, line.no, 'note line outside a block')
            step.note = (t[len('note'):].strip(), line.no)
            continue
        if t in PART_MARKERS:
            pending_markers.append((t, line.no))
            continue
        if head in ('suppose', 'let', 'assume'):
            lab = re.search(rf'\(({LABEL})\)$', t)
            if not lab:
                raise Problem(path, line.no, f'{head} line carries no label')
            pending_openers.append((head, t, lab.group(1), line.no))
            continue
        if head == 'requires':
            if step is None:
                raise Problem(path, line.no, 'requires line outside a step')
            body = t[len('requires'):].strip()
            if ':' not in body:
                raise Problem(path, line.no, 'requires line has no justification')
            fact, just = body.split(':', 1)
            step.requires.append((fact.strip(), just.strip(), line.no))
            continue
        if step is not None and step.just is None:
            if any(t.startswith(h) for h in HEADS):
                step.just = parse_justification(path, line)
            else:
                claim.claim.append(t)          # the claim runs on
            continue
        if step is not None and step.just is not None:
            if step.just.head == 'calculation':
                step.just.refs.extend(chain_citation(path, line))
                step.just.chain.append((line.text, line.no))
                continue
            raise Problem(path, line.no,
                          f'unexpected line after a justification: {t[:48]!r}')
        raise Problem(path, line.no, f'unexpected line {t[:48]!r}')
    close_step()
    return theorems


CHAIN_TAIL = re.compile(rf'({REF})(?:,\s*right to left)?$')


def chain_citation(path, line):
    """A chain line's citation, read from the right end of the line rather than
    from the whitespace that happens to separate it."""
    m = CHAIN_TAIL.search(line.text)
    if not m:
        raise Problem(path, line.no,
                      'chain line names no line or label; a chain only joins, '
                      'so every line must cite a numbered step or a label')
    return [m.group(1)]


def fmt(number):
    return '.'.join(str(x) for x in number)


def check_encoding(path, raw):
    """UTF-8 in Form C. Returns the decoded text."""
    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError as e:
        raise Problem(path, 1, f'not valid UTF-8: {e}') from e
    if unicodedata.normalize('NFC', text) != text:
        for no, ln in enumerate(text.split('\n'), 1):
            if unicodedata.normalize('NFC', ln) != ln:
                raise Problem(path, no, 'not in Unicode Normalisation Form C')
    return text
