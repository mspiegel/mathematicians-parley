"""What a set.mm label expects on the proof stack.

A Metamath proof is written in reverse Polish, and a step pushes the label's
mandatory floating hypotheses in order, then its essential hypotheses in
order. That order is not the order the variables appear in the statement: it
is the order their `$f` declarations appear in the file. Nothing but the
database knows it, so this module reads it.

Only the shape is read, never the proofs, so a pass over set.mm costs a few
seconds and no verification. `mmverify.py` does the same thing as part of
checking a proof; this is the part of it the elaborator needs.

Finding the file is here too, because four tools need it and none of them is
the natural owner of the other three.
"""
import os
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def where_set_mm(argv):
    """The library, said on the command line, in the environment, or here."""
    for said in (argv[1] if len(argv) > 1 else None, os.environ.get('SET_MM'),
                 ROOT / 'set.mm'):
        if said and Path(said).exists():
            return Path(said)
    return None


@dataclass
class Signature:
    """One label: what it concludes and what it wants pushed."""
    label: str
    kind: str                                  # '$a' or '$p'
    statement: list
    floats: list = field(default_factory=list)   # (typecode, variable), in order
    essentials: list = field(default_factory=list)
    disjoint: set = field(default_factory=set)

    @property
    def push(self):
        """The variables to push, in order."""
        return [v for _, v in self.floats]

    def bound(self):
        """The variable a binder in this statement introduces, if one does."""
        for typecode, var in self.floats:
            if typecode == 'setvar':
                return var
        return None


class Scope:
    def __init__(self):
        self.variables = set()
        self.floats = []          # (typecode, variable)
        self.essentials = []
        self.disjoint = set()


def _tokens(text):
    """Every whitespace-separated token, with comments and includes removed.

    Comments nest in Metamath, so the depth is counted rather than matched.
    An include names a file rather than saying anything, and the caller
    supplies the files it wants read, so the directive is dropped."""
    out, depth, including = [], 0, False
    for tok in text.split():
        if tok == '$(':
            depth += 1
        elif tok == '$)':
            depth = max(0, depth - 1)
        elif depth:
            continue
        elif tok == '$[':
            including = True
        elif tok == '$]':
            including = False
        elif not including:
            out.append(tok)
    return out


def read(path, *more):
    """Every label in the files, as a Signature.

    Includes are not followed. A file that includes another is read by
    passing both, in the order the includes would have reached them: the
    tokens become one stream, which is what an include means. set.mm
    includes nothing, so reading it alone needs no second path."""
    toks = []
    for one in (path, *more):
        with open(one, encoding='ascii') as f:
            toks.extend(_tokens(f.read()))

    stack, out = [Scope()], {}
    i, n = 0, len(toks)
    label = None
    while i < n:
        tok = toks[i]
        if tok == '${':
            stack.append(Scope())
            i += 1
        elif tok == '$}':
            stack.pop()
            i += 1
        elif tok in ('$v', '$c', '$d', '$f', '$e', '$a', '$p'):
            end = toks.index('$.', i) if tok != '$p' else toks.index('$=', i)
            body = toks[i + 1:end]
            _statement(stack, out, tok, label, body)
            label = None
            i = (toks.index('$.', end) if tok == '$p' else end) + 1
        else:
            label = tok
            i += 1
    return out


def _statement(stack, out, kind, label, body):
    top = stack[-1]
    if kind == '$v':
        top.variables.update(body)
    elif kind == '$c':
        pass
    elif kind == '$d':
        top.disjoint.update((min(a, b), max(a, b))
                            for a in body for b in body if a != b)
    elif kind == '$f':
        top.floats.append((body[0], body[1]))
        # A float is pushed by label like anything else, and proves that its
        # variable is of its type, so it is recorded with the rest.
        out[label] = Signature(label, '$f', body)
    elif kind == '$e':
        top.essentials.append(body)
    else:                                   # $a or $p
        out[label] = _assertion(stack, kind, label, body)


def _assertion(stack, kind, label, body):
    """The mandatory hypotheses of one assertion, in push order."""
    active = set().union(*(s.variables for s in stack)) if stack else set()
    essentials = [e for s in stack for e in s.essentials]
    wanted = {t for hyp in (*essentials, body) for t in hyp if t in active}
    floats = []
    for s in stack:
        for typecode, var in s.floats:
            if var in wanted:
                floats.append((typecode, var))
                wanted.discard(var)
    pairs = {p for s in stack for p in s.disjoint}
    names = {t for hyp in (*essentials, body) for t in hyp if t in active}
    return Signature(label, kind, body, floats, essentials,
                     {p for p in pairs if p[0] in names and p[1] in names})
