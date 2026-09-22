#!/usr/bin/env python3
"""Find a caller that uses a decline without asking whether it has one.

`parse.Declined` is what a route gives back when it does not apply. It is
truthy and is not a string so that a caller who forgets to look fails at the
line that forgot: `spell.seq` joins what it is given, and a decline reaching
it raises rather than shortening a proof and saying nothing.

That failure is loud but late — it waits for a proof to take the route. Eight
such callers were found that way, one at a time, over three commits. This
finds them by reading instead, which is why it is in the gate.

What it looks for is one shape: a call to something that can give back a
decline, used directly as an argument to another call. Anything bound to a
name first is left alone, because the name can be asked about and usually is.

Two things it must not confuse, both learnt from a false positive:

  - A function that builds a closure and gives the closure back does not
    itself decline. `not_zero` is one, so its returns are read without
    descending into the function nested in it.
  - A name given back after `declined` has been asked about it is a proof,
    not a decline. `required` reads a `requires` line, asks, and raises.

Usage:  parley/declines.py [file ...]
Exits non-zero when anything is found.
"""
import ast
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# What a decline is built by, wherever it is written.
BUILDERS = frozenset({'Declined', 'no'})


def called(node):
    """The bare name of what a call calls, however it is reached."""
    func = node.func
    if isinstance(func, ast.Attribute):
        return func.attr
    if isinstance(func, ast.Name):
        return func.id
    return None


def own_body(fn):
    """A function's own nodes, not those of the functions inside it."""
    out, stack = [], list(fn.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            continue
        out.append(node)
        stack.extend(ast.iter_child_nodes(node))
    return out


def declines(fn, known):
    """Whether this function can give a decline back to its caller."""
    asked = {node.args[0].id for node in own_body(fn)
             if isinstance(node, ast.Call) and called(node) == 'declined'
             and node.args and isinstance(node.args[0], ast.Name)}
    held = {node.targets[0].id for node in own_body(fn)
            if isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.Call)
            and called(node.value) in known}
    for node in own_body(fn):
        if not isinstance(node, ast.Return) or node.value is None:
            continue
        said = node.value
        if isinstance(said, ast.Call) and called(said) in known | BUILDERS:
            return True
        if isinstance(said, ast.Name) and said.id in held - asked:
            return True
    return False


def sites(path):
    """Every call in the file that hands a decline straight on."""
    tree = ast.parse(Path(path).read_text(encoding='utf-8'))
    functions = [n for n in ast.walk(tree)
                 if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    by_name = {}
    for fn in functions:
        by_name.setdefault(fn.name, []).append(fn)

    # A function declines if it gives back what a declining one gave it, so
    # the set is closed by going round until it stops growing.
    known, growing = set(), True
    while growing:
        growing = False
        for name, defs in by_name.items():
            if name not in known and any(declines(fn, known) for fn in defs):
                known.add(name)
                growing = True

    spans = sorted((n.lineno, n.end_lineno, n.name) for n in functions)

    def owner(line):
        found = None
        for start, end, name in spans:
            if start <= line <= end and (found is None or start > found[0]):
                found = (start, name)
        return found[1] if found else '?'

    out = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or called(node) == 'declined':
            continue
        for arg in [*node.args, *(k.value for k in node.keywords)]:
            if isinstance(arg, ast.Call) and called(arg) in known:
                out.append((arg.lineno, owner(arg.lineno), called(arg),
                            called(node)))
    return out


def main(argv):
    wanted = argv[1:] or sorted(str(p) for p in (ROOT / 'parley').glob('*.py'))
    total = 0
    for path in wanted:
        # Said from the root where the file is under it, and in full where a
        # caller has pointed this at something else, as one comparing two
        # revisions does.
        whole = Path(path).resolve()
        said = (whole.relative_to(ROOT) if whole.is_relative_to(ROOT)
                else whole)
        for line, owner, inner, outer in sorted(sites(path)):
            print(f'{said}:{line}  {owner} hands what {inner} gave it '
                  f'straight to {outer}, without asking whether it declined')
            total += 1
    print(f'\n{total} caller(s) use a decline without asking')
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
