#!/usr/bin/env python3
"""Find a caller that uses a decline without asking whether it has one.

`parse.Declined` is what a route gives back when it does not apply. It is
truthy and is not a string so that a caller who forgets to look fails at the
line that forgot: `spell.seq` joins what it is given, and a decline reaching
it raises rather than shortening a proof and saying nothing.

That failure is loud but late — it waits for a proof to take the route, and a
route no proof in the corpus takes never fails at all. Elaborating with
`settle` held to less than its depth takes routes the corpus does not, and
five callers failed there that nothing had reported. This finds them by
reading instead, which is why it is in the gate.

What it looks for is what can give back a decline, used where it is not
asked about: passed to a call, directly or with `*`; or bound to a name that
is then passed to a call, stored in a dictionary, written into an f-string,
or taken apart as a tuple, in a function that never asks `declined` about
the name. Asking `is None` is not asking, and an f-string is the worst of
them, because a decline has a message and becomes that text without a word.

What can give back a decline is closed across files, and a call is looked
for where it is: on `self`, in the file itself and in the methods of the
classes it inherits from or is inherited by in other files, since those are
one object; by a name the file defines, in the file itself; on a module, in
that module; on anything else, in the other files. By name alone,
`targets.unfolding` would be `elaborate.py`'s method of the same name, and
`work.normalize` in `elaborate.py` would be nothing.

Things it must not confuse, each learnt from a false positive:

  - A function that builds a closure and gives the closure back does not
    itself decline. `not_zero` is one, so its returns are read without
    descending into the function nested in it.
  - A name given back under `if declined(name):` is the decline; one given
    back after being asked about some other way is a proof. `required`
    reads a `requires` line, asks, and raises.
  - Asking through a loop, `for one in (a, b): if declined(one)`, asks
    about each; and a tuple is asked about through whichever of its names
    carries the decline, as `where, frame = self.allowed(...)` is.
  - The parser's `no` gives back None to backtrack and builds nothing, so
    what builds a decline is `Declined` and whatever gives one back.

Usage:  parley/declines.py [file ...]
Exits non-zero when anything is found.
"""
import ast
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# What a decline is built by, wherever it is written. A helper that builds
# one, as `elaborate.py`'s `no` does, is found the way any declining function
# is; naming it here would take in the parser's `no` too, which gives back
# None to backtrack and builds nothing.
BUILDERS = frozenset({'Declined'})


def called(node):
    """The bare name of what a call calls, however it is reached."""
    func = node.func
    if isinstance(func, ast.Attribute):
        return func.attr
    if isinstance(func, ast.Name):
        return func.id
    return None


def hits(call, known):
    """Whether a call reaches a function that can decline.

    `known` is the file's own such functions, those of the others, every
    name the file defines, the modules it imports, and its kin: the declining
    methods of classes in other files that its own classes inherit from or
    are inherited by. A call on `self` is the file's own or its kin's; a call
    of a name the file defines is the file's own; any other is another
    file's, and is looked for there.
    By name alone `targets.unfolding` would be `elaborate.py`'s
    `self.unfolding`, which declines where the other does not; `field.py`'s
    polynomials have a `power` of their own; and `work.normalize_quotient`
    would be nothing, since `elaborate.py` defines no such thing.
    """
    own, others, defined, modules, kin = known
    elsewhere = frozenset().union(*others.values())
    func = call.func
    if isinstance(func, ast.Attribute):
        name = func.attr
        if isinstance(func.value, ast.Name) and func.value.id == 'self':
            return name in own or name in kin
        # A module names its file, and nothing else is guessed at.
        if isinstance(func.value, ast.Name) and func.value.id in modules:
            return name in others.get(modules[func.value.id], ())
    elif isinstance(func, ast.Name):
        name = func.id
    else:
        return False
    return name in own if name in defined else name in elsewhere


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


def asked_about(fn):
    """The names a function asks `declined` about.

    Asking through a loop asks about each name the loop runs over:
    `for one in (alike, stated): if declined(one)` asks about both.
    """
    asked = {node.args[0].id for node in own_body(fn)
             if isinstance(node, ast.Call) and called(node) == 'declined'
             and node.args and isinstance(node.args[0], ast.Name)}
    for node in own_body(fn):
        if (isinstance(node, ast.For) and isinstance(node.target, ast.Name)
                and node.target.id in asked
                and isinstance(node.iter, (ast.Tuple, ast.List))):
            asked |= {one.id for one in node.iter.elts
                      if isinstance(one, ast.Name)}
    return asked


def held_from(fn, known):
    """The names a function binds to what a declining call gave it, with
    where each is bound. A tuple taken apart binds each of its names: the
    first of `where, frame = self.allowed(...)` is the decline.
    """
    out = {}
    for node in own_body(fn):
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.value, ast.Call)
                and hits(node.value, known)):
            continue
        target = node.targets[0]
        names = ([target] if isinstance(target, ast.Name)
                 else [t for t in getattr(target, 'elts', ())
                       if isinstance(t, ast.Name)])
        for name in names:
            out.setdefault(name.id, (node.lineno, called(node.value)))
    return out


def declines(fn, known):
    """Whether this function can give a decline back to its caller.

    A name given back under `if declined(name):` is the decline itself,
    whatever else the function asks about it: `apply_lemma` hands back the
    scope `allowed` refused in just that way.
    """
    asked = asked_about(fn)
    held = held_from(fn, known)
    for node in own_body(fn):
        if (isinstance(node, ast.If) and isinstance(node.test, ast.Call)
                and called(node.test) == 'declined' and node.test.args
                and isinstance(node.test.args[0], ast.Name)):
            name = node.test.args[0].id
            if any(isinstance(one, ast.Return)
                   and isinstance(one.value, ast.Name)
                   and one.value.id == name for one in node.body):
                return True
        if not isinstance(node, ast.Return) or node.value is None:
            continue
        said = node.value
        if isinstance(said, ast.Call) and (hits(said, known)
                                           or called(said) in BUILDERS):
            return True
        if isinstance(said, ast.Name) and said.id in set(held) - asked:
            return True
    return False


def functions_of(tree):
    return [n for n in ast.walk(tree)
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]


def modules_of(tree):
    """Each module the file imports whole, by the name it is used under."""
    out = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for one in node.names:
                out[one.asname or one.name] = one.name
    return out


def classes_of(tree):
    """Each class a file defines: the names of its bases, and its methods."""
    return {node.name: ({base.id for base in node.bases
                         if isinstance(base, ast.Name)},
                        {fn.name for fn in node.body
                         if isinstance(fn, (ast.FunctionDef,
                                            ast.AsyncFunctionDef))})
            for node in ast.walk(tree) if isinstance(node, ast.ClassDef)}


def declining(tree, others=None, kin=frozenset()):
    """The names of the functions in a file that can give back a decline.

    `others` is what declines in each other file, by module name, and `kin`
    what declines among the methods of this file's classes' relatives in
    other files. A function declines if it gives back what a declining one
    gave it, so the set is closed by going round until it stops growing.
    """
    others = others or {}
    by_name = {}
    for fn in functions_of(tree):
        by_name.setdefault(fn.name, []).append(fn)
    modules = modules_of(tree)
    own, growing = set(), True
    while growing:
        growing = False
        for name, defs in by_name.items():
            if name not in own and any(
                    declines(fn, (own, others, set(by_name), modules, kin))
                    for fn in defs):
                own.add(name)
                growing = True
    return own


def sites(path, others=None, kin=frozenset()):
    """Every call in the file that hands a decline straight on.

    `others` is what declines in each other file, by module name, which a
    call on anything but `self` is looked for in; `kin` is what declines
    among the methods a call on `self` may reach in other files.
    """
    others = others or {}
    tree = ast.parse(Path(path).read_text(encoding='utf-8'))
    functions = functions_of(tree)
    known = (declining(tree, others, kin), others,
             {fn.name for fn in functions}, modules_of(tree), kin)

    spans = sorted((n.lineno, n.end_lineno, n.name) for n in functions)

    def owner(line):
        found = None
        for start, end, name in spans:
            if start <= line <= end and (found is None or start > found[0]):
                found = (start, name)
        return found[1] if found else '?'

    out = []
    for node in ast.walk(tree):
        # A decline written into an f-string is its message, which is text
        # and raises nothing: `f'{self.binder_var(name)} cv'` would make one
        # a kernel name and say nothing.
        if (isinstance(node, ast.FormattedValue)
                and isinstance(node.value, ast.Call)
                and hits(node.value, known)):
            out.append((node.lineno, owner(node.lineno), called(node.value),
                        'an f-string'))
        if not isinstance(node, ast.Call) or called(node) == 'declined':
            continue
        for arg in [*node.args, *(k.value for k in node.keywords)]:
            # `f(*g())` spreads what g gave, and a decline spread fails no
            # louder than one passed whole.
            if isinstance(arg, ast.Starred):
                arg = arg.value
            if isinstance(arg, ast.Call) and hits(arg, known):
                out.append((arg.lineno, owner(arg.lineno), called(arg),
                            called(node)))

    # The same decline bound to a name first, where the function never asks
    # `declined` about the name. Asking `is None` is not asking: five callers
    # of `apply_lemma` did that, and one stored what it was given as a fact.
    for fn in functions:
        asked = asked_about(fn)
        held = held_from(fn, known)
        # A tuple taken apart is asked about through whichever of its names
        # carries the decline; the others are what came with it.
        for node in own_body(fn):
            if (isinstance(node, ast.Assign) and len(node.targets) == 1
                    and isinstance(node.targets[0], ast.Tuple)):
                names = {t.id for t in node.targets[0].elts
                         if isinstance(t, ast.Name)}
                if names & asked:
                    asked |= names
                # Taken apart where it arrives, with none of its names asked
                # about: the tuple was never a decline's to be, and a decline
                # arriving there is unpacked instead of asked.
                elif (isinstance(node.value, ast.Call)
                        and hits(node.value, known)):
                    out.append((node.lineno, fn.name, called(node.value),
                                'a tuple'))
        for node in own_body(fn):
            uses = []
            if isinstance(node, ast.Call) and called(node) != 'declined':
                uses = [(a, called(node))
                        for a in [*node.args, *(k.value for k in node.keywords)]]
            elif (isinstance(node, ast.Assign) and len(node.targets) == 1
                    and isinstance(node.targets[0], ast.Subscript)):
                uses = [(node.value, 'a dictionary')]
            elif isinstance(node, ast.FormattedValue):
                uses = [(node.value, 'an f-string')]
            for arg, into in uses:
                if (isinstance(arg, ast.Name) and arg.id in held
                        and arg.id not in asked):
                    _line, inner = held[arg.id]
                    out.append((node.lineno, fn.name, inner, into))
    return sorted(set(out))


def families(trees):
    """Which classes are one object: a class and everything it inherits from,
    or is inherited by, among the files given, by class name.
    """
    classes = {name: bases for tree in trees.values()
               for name, (bases, _methods) in classes_of(tree).items()}
    root = {name: name for name in classes}

    def find(name):
        while root[name] != name:
            name = root[name]
        return name

    for name, bases in classes.items():
        for base in bases & set(classes):
            root[find(base)] = find(name)
    return {name: find(name) for name in classes}


def across(paths):
    """What declines in each file, given what declines in all the others:
    by module for a call on a module or a bare name, and among the methods of
    its classes' relatives for a call on `self`.

    `elaborate.py` calls into `normal.py`, and a function there that gives
    back what one here gave it declines too, so the files are closed
    together until none of them grows.
    """
    trees = {p: ast.parse(Path(p).read_text(encoding='utf-8')) for p in paths}
    own = {p: set() for p in paths}
    family = families(trees)
    methods = {p: {(family[name], method)
                   for name, (_bases, defs) in classes_of(tree).items()
                   for method in defs}
               for p, tree in trees.items()}

    def others(p):
        return {Path(q).stem: frozenset(own[q]) for q in paths if q != p}

    def kin(p):
        mine = {one for one, _method in methods[p]}
        return frozenset(method for q in paths if q != p
                         for one, method in methods[q]
                         if one in mine and method in own[q])

    growing = True
    while growing:
        growing = False
        for p, tree in trees.items():
            found = declining(tree, others(p), kin(p))
            if found != own[p]:
                own[p], growing = found, True
    return {p: (others(p), kin(p)) for p in paths}


def main(argv):
    wanted = argv[1:] or sorted(str(p) for p in (ROOT / 'parley').glob('*.py'))
    # Another file's functions are read wherever this one calls them, even
    # when only this one is asked about.
    everything = sorted({*wanted,
                         *(str(p) for p in (ROOT / 'parley').glob('*.py'))})
    seen = across(everything)
    total = 0
    for path in wanted:
        # Said from the root where the file is under it, and in full where a
        # caller has pointed this at something else, as one comparing two
        # revisions does.
        whole = Path(path).resolve()
        said = (whole.relative_to(ROOT) if whole.is_relative_to(ROOT)
                else whole)
        for line, owner, inner, outer in sorted(sites(path, *seen[path])):
            print(f'{said}:{line}  {owner} hands what {inner} gave it '
                  f'straight to {outer}, without asking whether it declined')
            total += 1
    print(f'\n{total} caller(s) use a decline without asking')
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
