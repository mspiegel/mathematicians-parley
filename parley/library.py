"""What a set.mm label expects on the proof stack.

A Metamath proof is written in reverse Polish, and a step pushes the label's
mandatory floating hypotheses in order, then its essential hypotheses in
order. That order is not the order the variables appear in the statement: it
is the order their `$f` declarations appear in the file. Nothing but the
database knows it, so this module reads it.

Only the shape is read, never the proofs, so a pass over set.mm costs a few
seconds and no verification. `mmverify.py` does the same thing as part of
checking a proof; this is the part of it the elaborator needs.
"""
from dataclasses import dataclass, field


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
    def arity(self):
        return len(self.floats) + len(self.essentials)

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
    """Every whitespace-separated token, with comments removed.

    Comments nest in Metamath, so the depth is counted rather than matched."""
    out, depth = [], 0
    for tok in text.split():
        if tok == '$(':
            depth += 1
        elif tok == '$)':
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(tok)
    return out


def read(path):
    """Every label in the file, as a Signature.

    Included files are not followed. set.mm includes nothing, and a file that
    includes it is read by passing set.mm itself."""
    with open(path, encoding='ascii') as f:
        toks = _tokens(f.read())

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
