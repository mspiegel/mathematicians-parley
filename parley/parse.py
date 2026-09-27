"""Parse the database files and the proof skeletons described by GRAMMAR.md.

A claim is an opaque run of text. Nothing here looks inside a formula.
"""
import re
import unicodedata
from dataclasses import dataclass, field

NAME = r'[A-Za-z][A-Za-z0-9-]*'
# What follows `def:` or `thm:`: an item's name, spelt with the path of the
# file that holds it, or bare for a theorem of the file citing it.
CITED = rf'(?:{NAME}/)*{NAME}'
# The standard library, the one module root that is not a proof file: it is
# never imported, and every proof may cite it.
STDLIB = 'stdlib'
LABEL = r'[A-Z]+[0-9]*'
NUMBER = r'\d+(?:\.\d+)*'
REF = rf'(?:{NUMBER}|{LABEL})'

HEADS = ('def:', 'thm:', 'obtain', 'exhibit', 'substitute', 'instantiate',
         'algebra', 'arithmetic', 'inequalities', 'membership', 'join',
         'contradiction',
         'fix', 'induction', 'cases', 'calculation')
PART_MARKERS = ('base', 'step', 'case')
BLOCK_HEADS = ('contradiction', 'fix', 'induction', 'cases', 'calculation')


class Problem(Exception):
    """A defect found while reading. Carries where it was found.

    One of two, and the other is below. This one is a person's to fix: the
    proof text says something wrong, or a database record does, and nothing
    should carry on past it. Anything that catches this to try something
    else is accepting a proof with a defect in it.
    """

    def __init__(self, path, line, message):
        super().__init__(message)
        self.path, self.line, self.message = path, line, message

    def __str__(self):
        return f'{self.path}:{self.line}  {self.message}'


class Declined:
    """What a route gives back when it does not apply.

    Nobody's to fix, unlike the `Problem` above: a route that does not
    apply, a lemma that does not fit, an emitter with no shape for what it
    was given. What receives one tries the next way, or takes the step as
    stated and lists it at the head of the file. It is a value and not an
    exception, because nothing has gone wrong — a route asked whether it
    applies and saying no is the ordinary course of the day, and there is
    no other kind of failure here that an exception is then left to mean.

    Not None, which would be the obvious value, because `elaborate.py`
    already returns None at sixty-eight sites and already means several
    things by it: `renaming` returns it both for *nothing is spelt
    differently* and for *this cannot be done*, told apart only because
    callers test equality first. One more meaning there would move the
    double duty rather than end it.

    Truthy, and not a string. A proof is a string and `spell.seq` joins
    what it is given, dropping whatever is falsy, so a decline reaching it
    as None or as '' would shorten a proof and say nothing whatever. As
    this, the join raises at the call that forgot to look.

    The message is built only if something reads it, and most are read by
    nobody: a route declines, the caller tries the next, and writing a term
    out the way a Metamath file writes it is not cheap. Elaborating the
    geometric series declines over a million times, and rendering those was
    a third of what it cost.
    """

    __slots__ = ('shape', 'spell', 'terms')

    def __init__(self, shape, terms=(), spell=None):
        self.shape, self.terms, self.spell = shape, terms, spell

    def __bool__(self):
        return True

    def __str__(self):
        if self.spell is None:
            return self.shape
        return self.shape.format(*(self.spell(one) for one in self.terms))

    def __repr__(self):
        return f'Declined({str(self)!r})'


def declined(what):
    """Whether what came back is a route saying it does not apply."""
    return isinstance(what, Declined)


@dataclass
class Line:
    """One logical line: a physical line plus any continuations of it."""
    path: str
    no: int
    text: str
    indent: int


def read_lines(path, text):
    """Physical lines, comments and blanks dropped, joined by the continuation
    rule: a line continues onto the next when it ends with a comma.

    A `define` continues until the line carrying its label, because a
    function defined by cases writes one case to a line (`SYNTAX.md`). Its
    lines are joined keeping the break, which is what tells one case from
    the next: a value may hold a comma of its own, as gcd(a, b) does.
    """
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
            defining = pending.text.startswith('define ')
            pending.text += ('\n' if defining else ' ') + stripped
            if not (unlabelled(pending.text) if defining
                    else stripped.endswith(',')):
                out.append(pending)
                pending = None
            continue
        line = Line(path, no, stripped, indent)
        if stripped.endswith(',') or (stripped.startswith('define ')
                                      and unlabelled(stripped)):
            pending = line
        else:
            out.append(line)
    if pending:
        out.append(pending)
    return out


def unlabelled(text):
    """Whether a line ends without the label a define closes on."""
    return re.search(rf'\({LABEL}\)$', text) is None


# --------------------------------------------------------------- database

@dataclass
class Record:
    kind: str
    name: str
    fields: dict = field(default_factory=dict)
    hypotheses: list = field(default_factory=list)
    conclusions: list = field(default_factory=list)
    repeats: list = field(default_factory=list)   # (field, line) said twice
    lines: dict = field(default_factory=dict)     # field -> line it is on
    line: int = 0
    path: str = ''

    @property
    def module(self):
        return module_of(self.path)


def module_of(path):
    """The module a file is: its path from the root without the extension."""
    return str(path).rsplit('.', 1)[0]


def qualified(item):
    """An item's full name: its file's module, then its own name."""
    return f'{item.module}/{item.name}'


def resolve(cited, module):
    """The full name a citation means, cited from a file of `module`.

    A spelt name is taken as written; a bare one is a theorem of the citing
    file. Whether anything has that name is the caller's to ask.
    """
    return cited if '/' in cited else f'{module}/{cited}'


def cited_name(head):
    """The name a `def:` or `thm:` head cites, without its prefix."""
    return head.split(':', 1)[1]


def in_stdlib(name):
    return name.startswith(STDLIB + '/')


RECORD_KINDS = ('notation', 'method', 'definition', 'theorem', 'precedence')

# The fields each kind of record may carry, as the header of each records
# file describes them. A field outside its kind's list is refused: the tools
# read fields by name, so a misspelt `target` is not a target, and the item
# it belongs to would be taken as stated wherever it is cited. A precedence
# record is not listed, because its fields are the levels it declares.
FIELDS = {
    'notation': {'pattern', 'holes', 'yields', 'kinds', 'level', 'assoc',
                 'commutes', 'negates', 'spells', 'wraps', 'binds', 'reads',
                 'target', 'metamath', 'note'},
    'method': {'form', 'block', 'parts', 'parts-repeat', 'part-opens',
               'checks', 'decides', 'hypotheses', 'specified-in', 'metamath',
               'note'},
    'definition': {'metamath', 'target', 'open', 'symbol', 'defines', 'note'},
    'theorem': {'metamath', 'target', 'open', 'note'},
}


def parse_database(path, text):
    """Records of db/*.records. A record begins at column 0; its fields are
    indented. `let`, `assume` and `then` lines carry an item's statement.
    """
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
            # A field said twice is joined to the first, which is what a
            # wrapped line does and is not what a second field line means.
            # The join is kept so the record still reads, and the repeat is
            # recorded for the checker to refuse.
            if key in cur.fields:
                cur.repeats.append((key, line.no))
            cur.lines.setdefault(key, line.no)
            cur.fields[key] = (cur.fields[key] + ' ' + value
                               if key in cur.fields else value)
    return records


# ------------------------------------------------------------------ proofs

@dataclass
class Justification:
    head: str            # 'def:stdlib/numbers/sqrt', 'thm:foo', or a method name
    text: str
    line: int
    refs: list = field(default_factory=list)      # everything cited, in order
    target: str = None                            # instantiate's `in ...`
    instantiations: list = field(default_factory=list)
    chain: list = field(default_factory=list)     # (text, line) of a calculation
    bad_ref: str = None       # a `from` entry that is neither a line nor a label
    module: str = ''          # of the file it is written in, which a bare name means
    defined: str = None       # the define's label, where the head is `define`

    def item(self, cited):
        """The full name a citation written in this justification's file means."""
        return resolve(cited_name(cited), self.module)


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
    part_notes: dict = field(default_factory=dict)  # part index -> (text, line)


DEFINED = re.compile(
    r'^define\s+(?P<name>[^\s(]+)(?:\((?P<param>[^\s()]+)\))?\s*:=\s*'
    r'(?P<body>.+?)(?:,\s*for\s+(?P<over>\S+)\s*(?P<how>[∈⊆])\s*'
    r'(?P<domain>.+))?$', re.S)
# One line of a define by cases: a value and the condition it is taken
# under, or the last value, taken `otherwise`.
CASE = re.compile(r'^(?P<value>.+?)\s+if\s+(?P<condition>.+)$', re.S)
OTHERWISE = re.compile(r'^(?P<value>.+?)\s+otherwise$', re.S)


def by_cases(lines):
    """The lines of a define by cases as one term: each value and its
    condition, nested from the right into `_ if _, _ otherwise`; or a
    decline saying which line is not a case.
    """
    last = OTHERWISE.match(lines[-1])
    if last is None:
        return Declined('the last line of a define by cases is its value '
                        '`otherwise`')
    term, nested = last.group('value').strip(), False
    for line in reversed(lines[:-1]):
        case = CASE.match(line)
        if case is None:
            return Declined(f'{line!r} is not a case: write the value, then '
                            f'`if` and the condition it is taken under')
        rest = f'({term})' if nested else term
        term = (f'{case.group("value").strip()} if '
                f'{case.group("condition").strip()}, {rest} otherwise')
        nested = True
    return term


@dataclass
class Define:
    """What a `define` line says: a name, and the term it stands for.

    A name with a parameter is a function, as a reader writes "S(m) = 1 + 2
    + … + m": `define S(m) := Σ(j = 1 to m) j, for m ∈ ℕ`. Its domain is
    said with it, because a rule without one says what S does and not where
    S is defined.
    """
    name: str
    body: str
    param: str = None
    domain: str = None

    @property
    def names(self):
        """The names the define gives, as a `Recursion` has them."""
        return [self.name]


@dataclass
class Recursion:
    """What a `define` of sequences by recursion says: each name's value at
    0, and its value at k + 1 in terms of the values at k.

    `define a(0) := M, b(0) := N, a(k + 1) := b(k), b(k + 1) := a(k) mod
    b(k), for k ∈ ℕ₀` defines two sequences together, as a textbook writes
    Euclid's algorithm; one name alone is the same form with one sequence.
    `start` and `step` hold each name's rule as written, a rule by cases
    already folded into `_ if _, _ otherwise` as `Define` folds one.
    """
    names: list
    index: str
    domain: str
    start: dict
    step: dict


# A sequence is named as a variable is: a letter, perhaps with a subscript
# or a prime.
SEQUENCE_NAME = r'[A-Za-zα-ω][₀-₉′]*'
# The head of one rule of a recursion: a name, the index it is said at, and
# `:=`. A rule runs to the next head or to the closing `for`.
RECURSIVE_HEAD = re.compile(
    rf'(?:^|,)\s*(?P<name>{SEQUENCE_NAME})\((?P<at>[^()]*)\)\s*:=', re.S)
RECURSIVE_FOR = re.compile(
    r',\s*for\s+(?P<index>\S+)\s*∈\s*(?P<domain>\S+)\s*$', re.S)


def rule_term(text):
    """One rule's text as a term: its lines joined, or folded by cases
    where its last line is taken `otherwise`.
    """
    pieces = [p.strip() for p in text.strip().rstrip(',').split('\n')]
    if len(pieces) > 1 and OTHERWISE.match(pieces[-1]):
        return by_cases(pieces)
    return ' '.join(pieces)


def recursion_parts(said):
    """A define of sequences by recursion, without its label, read into its
    parts; or a decline saying what is wrong with it.
    """
    closing = RECURSIVE_FOR.search(said)
    if closing is None:
        return Declined('a define by recursion ends `, for k ∈ ℕ₀`, naming '
                        'the index its rules are written in')
    index, domain = closing.group('index'), closing.group('domain')
    if domain != 'ℕ₀':
        return Declined(f'a define by recursion starts at 0, so its index '
                        f'runs over ℕ₀, not {domain}')
    body = said[len('define'):closing.start()]
    heads = list(RECURSIVE_HEAD.finditer(body))
    names, start, step = [], {}, {}
    for head, after in zip(heads, [*heads[1:], None], strict=True):
        name, at = head.group('name'), ' '.join(head.group('at').split())
        rule = rule_term(body[head.end():after.start() if after else None])
        if declined(rule):
            return rule
        if at == '0':
            table = start
        elif at == f'{index} + 1':
            table = step
        else:
            return Declined(f'{name}({at}) is neither {name}(0) nor '
                            f'{name}({index} + 1): a rule gives a value at 0 '
                            f'or at the step')
        if name in table:
            return Declined(f'{name}({at}) is given twice')
        table[name] = rule
        if name not in names:
            names.append(name)
    for name in names:
        if name not in start:
            return Declined(f'{name} has no value at 0')
        if name not in step:
            return Declined(f'{name} has no rule for {name}({index} + 1)')
    return Recursion(names, index, domain, start, step)


def define_parts(text):
    """A `define` line, without its label, read into its parts; or a
    decline saying what is wrong with it. A define whose first rule is said
    at 0 is a recursion (`Recursion`); any other is one name (`Define`).
    """
    said = re.sub(rf'\s*\({LABEL}\)\s*$', '', text).strip()
    if re.match(rf'^define\s+{SEQUENCE_NAME}\(0\)\s*:=', said):
        return recursion_parts(said)
    m = DEFINED.match(said)
    if m is None or not m.group('body').strip():
        return Declined('a define says `define <name> := <term>`')
    param, over = m.group('param'), m.group('over')
    body = m.group('body').strip()
    # A define over several lines is either one term wrapped by the comma
    # rule, or a function by cases, one case to a line.
    pieces = [p.strip() for p in body.split('\n')]
    if len(pieces) > 1 and OTHERWISE.match(pieces[-1]):
        body = by_cases(pieces)
        if declined(body):
            return body
    else:
        body = ' '.join(pieces)
    if param is not None and over is None:
        return Declined(f'define {m.group("name")}({param}) says no domain: '
                        f'write `, for {param} ∈ …` after its rule')
    if param is None and over is not None:
        return Declined(f'define {m.group("name")} gives a domain and takes '
                        f'no argument')
    if param is not None and over != param:
        return Declined(f'define {m.group("name")}({param}) gives the domain '
                        f'of {over}')
    # `for X ⊆ A` is `for X ∈ 𝒫A`: X runs over the parts of A.
    domain = ' '.join(m.group('domain').split()) if param else None
    if domain and m.group('how') == '⊆':
        domain = f'𝒫{domain}' if ' ' not in domain else f'𝒫({domain})'
    return Define(m.group('name'), body, param, domain)


class FileScope:
    """What a proof file holds outside its theorems: the definitions it
    writes between them, and the definitions it imports from other files.

    A theorem sees the definitions written above it and every one its file
    imports (`visible`). An imported one is read in the file that wrote it,
    which is why each carries the scope it comes from.
    """

    def __init__(self, path):
        self.path = path
        self.defines = []     # ('define', text, label, line), as written
        self.readings = {}    # define label -> (text, line)
        self.imports = []     # (module, name, alias, line, label)
        self.linked = {}      # alias -> (FileScope, define), `link_definitions`

    def visible(self, line):
        """(name, define, the scope it is read in) for every definition a
        line of this file at `line` may use.
        """
        out = [(alias, d, src) for alias, (src, d) in self.linked.items()]
        for d in self.defines:
            if d[3] < line:
                said = define_parts(d[1])
                if not declined(said):
                    out.append((said.name, d, self))
        return out

    def import_label(self, alias):
        """The label the import writing a definition as `alias` carries."""
        return next(label for _m, _n, a, _no, label in self.imports
                    if a == alias)

    def written(self, name):
        """The define this file writes at file level under `name`; else None."""
        for d in self.defines:
            said = define_parts(d[1])
            if not declined(said) and said.name == name:
                return d
        return None


def link_definitions(theorems):
    """Point every definition import at the define it names, and say what
    does not resolve: (path, line, message) for each.
    """
    scopes = {}
    for thm in theorems:
        scopes.setdefault(thm.module, thm.scope)
    problems = []
    for scope in scopes.values():
        scope.linked = {}
        for module, name, alias, no, _label in scope.imports:
            src = scopes.get(module)
            if src is None:
                problems.append((scope.path, no, f'import definition '
                                 f'{module}/{name} names no proof file'))
                continue
            d = src.written(name)
            if d is None:
                problems.append((scope.path, no, f'import definition '
                                 f'{module}/{name}: {module} defines no '
                                 f'{name} outside its theorems'))
                continue
            scope.linked[alias] = (src, d)
    return problems


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
    fields: dict = field(default_factory=dict)     # metamath, note
    imports: list = field(default_factory=list)    # (module, line) of its file
    scope: FileScope = None    # its file's definitions outside any theorem
    kind = 'theorem'

    @property
    def module(self):
        return module_of(self.path)


def written_text(thm):
    """Everything a theorem's lines say, as one run of text: the statement,
    its defines, and every step's claim, openers, requires lines and
    justification.
    """
    parts = [t for _k, t, _l, _n in thm.hypotheses] + [thm.conclusion]
    parts += [t for _k, t, _l, _n in thm.defines]
    for step in thm.steps:
        parts += list(step.claim)
        parts += [o[1] for o in step.openers]
        parts += [text for text, _how, _line in step.requires]
        if step.just:
            parts.append(step.just.text)
            parts += [text for text, _line in step.just.chain]
    return ' '.join(parts)


def outermost(words, relation):
    """Where a chain's first line puts its relation: the first time the
    symbol stands outside every bracket; None where it stands only inside.

    A sum binds its index with the same `=` a chain relates by, so
    `x·(Σ(k = 0 to m) t(k)) = …` has an `=` inside the sum before the one
    the chain means.
    """
    depth = 0
    for at, word in enumerate(words):
        if depth == 0 and word == relation:
            return at
        depth += sum(word.count(c) for c in '({[') \
            - sum(word.count(c) for c in ')}]')
    return None


THEOREM_FIELDS = ('metamath', 'note')


def citations(text):
    """The references a justification names, for a reader outside this file."""
    return references(text)[0]


# A justification that cites a define: its label, and what says which case.
DEFINE_CITED = re.compile(rf'^({LABEL})(?:\s*,\s*from\s+\S.*)?$')


def references(text):
    """References named by a justification, read from their syntactic position
    and never by scanning for digits, and the first `from` entry that is no
    reference (None where there is none). A step's justification and a
    requires line's are the same production, and both are read here.
    """
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


def cites_define(text, defines):
    """The define label a justification line cites as its head, or None.

    A define is cited by its label, alone or with `from`: `D2, from 4.1`.
    Only a whole line of that shape, and only a label a define in scope
    carries, since a claim may begin with a capital as a label does.
    """
    m = DEFINE_CITED.match(text)
    return m.group(1) if m and m.group(1) in defines else None


def parse_justification(path, line, defines=frozenset()):
    text = line.text
    head = next((h for h in HEADS if text.startswith(h)), None)
    label = cites_define(text, defines) if head is None else None
    if label is not None:
        j = Justification(head='define', text=text, line=line.no,
                          module=module_of(path), defined=label)
        j.refs, j.bad_ref = references(text)
        j.refs.insert(0, label)
        return j
    if head is None:
        raise Problem(path, line.no, f'no justification head in {text[:40]!r}')
    if head in ('def:', 'thm:'):
        m = re.match(rf'(?:def|thm):{CITED}', text)
        head = m.group(0)
    j = Justification(head=head, text=text, line=line.no, module=module_of(path))
    # A malformed justification is reported by the checker, not raised here: one
    # bad line must not cost the reader every later line in the file.
    j.refs, j.bad_ref = references(text)
    # A substitute names its equation's source in brackets after it. Only
    # there: M(C) on any other line is a function applied to C, not a
    # citation of a label C.
    src = re.match(rf'substitute\s.*\((?:line\s+({NUMBER})|({LABEL}))\)'
                   rf'(?:\s+into\s+\S.*?)?\s*$', text)
    if src:
        j.refs.append(src.group(1) or src.group(2))
    for dest in re.finditer(rf'\binto\s+(?:line\s+({NUMBER})|({LABEL}))\b', text):
        j.refs.append(dest.group(1) or dest.group(2))
    m = re.search(rf'\bin\s+(?:line\s+({NUMBER})|(def:{CITED})|({LABEL}))\b', text)
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

# The item an obtain takes its object from.
OBTAINED_FROM = re.compile(rf'^obtain\s+[^:]+:\s*((?:def|thm):{CITED})')
# A requires line's justification, where it cites an item.
REQUIRES_ITEM = re.compile(rf'^(def|thm):({CITED})')


def cited_item(just):
    """The item a step's justification cites, as `def:x` or `thm:x`, or None.

    Either the head is the item, or the step obtains from one:
    `obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7` owes
    the item's hypotheses as surely as a step headed by it does.
    """
    if not just:
        return None
    if just.head.startswith(('def:', 'thm:')):
        return just.head
    m = OBTAINED_FROM.match(just.text) if just.head == 'obtain' else None
    return m.group(1) if m else None


def cited_items(thm):
    """Every item a theorem's steps cite, by full name, with its line."""
    for step in thm.steps:
        just = step.just
        if not just:
            continue
        item = cited_item(just)
        if item:
            yield just.item(item), just.line
        if just.target and just.target.startswith('def:'):
            yield just.item(just.target), just.line
        for _fact, how, no in step.requires:
            m = REQUIRES_ITEM.match(how)
            if m:
                yield just.item(m.group(0)), no


IMPORTED = re.compile(
    rf'^import\s+(?:(?P<proof>proof)\s+(?P<module>{CITED})'
    rf'|(?P<definition>definition)\s+(?P<full>{CITED})'
    rf'(?:\s+as\s+(?P<alias>[^\s()]+))?'
    rf'(?:\s+\((?P<label>{LABEL})\))?)\s*$')


def importing(path, no, text):
    """One `import` line, as ('proof', module, line) or ('definition',
    module, name, alias, line).

    Every import says what it brings in: `import proof` a proof file, whose
    theorems the file may then cite by their full names, and `import
    definition` one definition, which the file then writes by its name, or
    by the name after `as`. Said on the line, a file and a definition never
    have to be told apart by what happens to exist.
    """
    m = IMPORTED.match(text.strip())
    if m is None:
        raise Problem(path, no, 'an import says `import proof <file>` or '
                                '`import definition <file>/<name>`')
    if m.group('proof'):
        return 'proof', m.group('module'), no
    module, _, name = m.group('full').rpartition('/')
    if not module:
        raise Problem(path, no, f'import definition {m.group("full")} names '
                                f'no file')
    # A definition a file imports is cited by its label, as one it defines
    # is: a calculation link writing S(k + 1) out cites the equation.
    if not m.group('label'):
        raise Problem(path, no, f'import definition {m.group("full")} '
                                f'carries no label')
    return ('definition', module, name, m.group('alias') or name, no,
            m.group('label'))


def parse_proof(path, text):
    """Theorems of a .proof file. Structure comes from the step number;
    indentation is presentation and is not consulted.
    """
    theorems, thm, step, claim, defined = [], None, None, None, None
    imports, scope = [], FileScope(path)

    def settle():
        """A define after a theorem's last step is the file's, for the
        theorems below it: that theorem could never use it.
        """
        if thm is None:
            return
        last = max((s.line for s in thm.steps), default=thm.line)
        for d in [d for d in thm.defines if d[3] > last]:
            thm.defines.remove(d)
            scope.defines.append(d)
            if d[2] in thm.readings:
                scope.readings[d[2]] = thm.readings.pop(d[2])
    # Between a theorem line and its statement a theorem may carry fields,
    # and a line there that opens no field continues the one above it.
    header, last_field = False, None
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
        the step numbered `number` sits in, and say which part it sits in.
        """
        parent = number[:-1]
        owner = by_number.get(parent)
        for marker, no, note in pending_markers:
            if owner is None:
                raise Problem(path, no, f'part marker {marker!r} outside any block')
            owner.parts.append((marker, no))
            part_no[parent] = part_no.get(parent, -1) + 1
            if note:
                owner.part_notes[part_no[parent]] = note
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
            settle()
            name = t[len('theorem '):].strip()
            if not re.fullmatch(NAME, name):
                raise Problem(path, line.no, f'theorem name {name!r} is malformed')
            thm = Theorem(name=name, line=line.no, path=path, imports=imports,
                          scope=scope)
            theorems.append(thm)
            pending_markers.clear()
            pending_openers.clear()
            part_no.clear()
            by_number.clear()
            header, last_field = True, None
            continue
        if thm is None:
            if t.startswith('import '):
                if scope.defines:
                    raise Problem(path, line.no,
                                  'an import below a define; imports come '
                                  'first')
                said = importing(path, line.no, t)
                if said[0] == 'proof':
                    imports.append(said[1:])
                else:
                    scope.imports.append(said[1:])
                continue
            # A define before any theorem is the file's, for every theorem.
            if t.startswith('define '):
                lab = re.search(rf'\(({LABEL})\)$', t)
                if not lab:
                    raise Problem(path, line.no, 'define line carries no label')
                parts = define_parts(t)
                if declined(parts):
                    raise Problem(path, line.no, str(parts))
                if isinstance(parts, Recursion):
                    raise Problem(path, line.no,
                                  'a define by recursion is written in the '
                                  'theorem that uses it, in its statement or '
                                  'its proof')
                scope.defines.append(('define', t, lab.group(1), line.no))
                defined = scope.defines[-1]
                continue
            if t.startswith('reads') and just_defined is not None:
                scope.readings[just_defined[2]] = (t[len('reads'):].strip(),
                                                   line.no)
                continue
            raise Problem(path, line.no,
                          'text before any theorem header that is neither an '
                          'import nor a define')

        head = t.split(None, 1)[0]
        if header and head in THEOREM_FIELDS:
            if head in thm.fields:
                raise Problem(path, line.no,
                              f'theorem {thm.name} says {head} twice')
            thm.fields[head] = t[len(head):].strip()
            last_field = (head, line.indent)
            continue
        if header and last_field and line.indent > last_field[1]:
            thm.fields[last_field[0]] += ' ' + t
            continue
        header = False

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
            parts = define_parts(t)
            if declined(parts):
                raise Problem(path, line.no, str(parts))
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
            # Under a part marker, the note says what that part does; the
            # marker is still held, because the step owning it is found only
            # when the part's first step arrives.
            if pending_markers:
                marker, no, held = pending_markers[-1]
                if held:
                    raise Problem(path, line.no,
                                  f'the {marker!r} part already carries a note')
                if pending_openers:
                    raise Problem(path, line.no,
                                  f'a note on the {marker!r} part goes directly '
                                  f'under its marker, before its openers')
                pending_markers[-1] = (marker, no,
                                       (t[len('note'):].strip(), line.no))
                continue
            if step is None or not step.just:
                raise Problem(path, line.no, 'note line outside a block')
            step.note = (t[len('note'):].strip(), line.no)
            continue
        if t in PART_MARKERS:
            pending_markers.append((t, line.no, None))
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
            defines = {d[2] for d in scope.defines + thm.defines} \
                | {d[-1] for d in scope.imports}
            if any(t.startswith(h) for h in HEADS) \
                    or cites_define(t, defines):
                step.just = parse_justification(path, line, defines)
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
    settle()
    return theorems


CHAIN_TAIL = re.compile(rf'(\barithmetic|{REF})$')


def chain_citation(path, line):
    """A chain line's citation, read from the right end of the line rather than
    from the whitespace that happens to separate it.

    A link relating numerals alone may name `arithmetic` in place of a line,
    and then it cites nothing: the fact is worked out where it stands.
    """
    m = CHAIN_TAIL.search(line.text)
    if not m:
        raise Problem(path, line.no,
                      'chain line names no line or label; a chain only joins, '
                      'so every line must cite a numbered step, a label, or '
                      '`arithmetic` for a link of numerals alone')
    return [] if m.group(1) == 'arithmetic' else [m.group(1)]


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


def record_files(root):
    """The database: notation and methods in db/, items in the library."""
    return [*sorted((root / 'db').glob('*.records')),
            *sorted((root / STDLIB).glob('*.records'))]


def proof_files(root):
    """Every readable proof under the root, wherever it is kept."""
    return sorted(p for p in root.rglob('*.proof')
                  if not any(part.startswith('.')
                             for part in p.relative_to(root).parts))


def corpus(root):
    """Every record and every readable proof, read from the working tree."""
    records = []
    for path in record_files(root):
        rel = str(path.relative_to(root))
        records.extend(parse_database(rel, check_encoding(rel,
                                                          path.read_bytes())))
    theorems = []
    for path in proof_files(root):
        rel = str(path.relative_to(root))
        theorems.extend(parse_proof(rel, check_encoding(rel,
                                                        path.read_bytes())))
    # What does not resolve is the checker's to report; here a definition
    # import that names nothing is simply one that brings nothing in.
    link_definitions(theorems)
    return records, theorems


def index(records, theorems):
    """Every definition and theorem by its full name.

    A theorem of a proof file is its own entry: the proof holds its
    statement. Where two share a name the first is kept, and the checker is
    what says there are two.
    """
    out = {}
    for item in records:
        if item.kind in ('definition', 'theorem'):
            out.setdefault(qualified(item), item)
    for thm in theorems:
        out.setdefault(qualified(thm), thm)
    return out


def proved(item):
    """Whether an item is proved by a readable proof of this corpus."""
    return isinstance(item, Theorem)
