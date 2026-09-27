"""Match an item's hypothesis against the fact a step supplies for it.

The match is one-way: the item is a pattern whose names stand for anything, and
the fact is ground. `thm:stdlib/sets/subset-transitive` assumes X ⊆ Y and
Y ⊆ Z, and a step citing it from two lines claiming S ⊆ [a, b] and
[a, b] ⊆ ℝ supplies them with X, Y, Z standing for S, [a, b] and ℝ. A name
that appears twice must stand for the same thing both times, which is what
makes the middle Y load-bearing.

A citation may write its instantiation and 69 of the corpus's 106 do. The
written pairs seed the binding, so they are checked rather than trusted, and a
citation that writes none is read the same way.
"""
import re

from formula import Node
from parse import LABEL

# An instantiation value may itself contain a comma, as `e := gcd(a, b)` does,
# so the list is split at the commas that sit outside brackets rather than by a
# pattern that stops at the first one.
ASSIGN = re.compile(r'([^\s,]+)\s*:=\s*(.+)')


def instantiation(text):
    """The `v := t` pairs of a justification, in order."""
    # An `instantiate` says where it lands, and that is a line, an item or a
    # bare label — the three `parse` reads for the target. A value stops at
    # whichever of them follows it, and `IH` is a label.
    body = re.split(rf',\s*from\b|\s+in\s+(?:line\b|def:|{LABEL}\b)',
                    text, maxsplit=1)[0]
    head = re.match(r'(?:def|thm):[^\s]+\s*|instantiate\s+', body)
    if head:
        body = body[head.end():]
    out = []
    for piece in split_commas(body):
        m = ASSIGN.match(piece.strip())
        if m:
            out.append((m.group(1).strip(), m.group(2).strip()))
    return out


def split_commas(text):
    """Split on the commas outside brackets."""
    out, depth, start = [], 0, 0
    for i, ch in enumerate(text):
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        elif ch == ',' and depth == 0:
            out.append(text[start:i])
            start = i + 1
    out.append(text[start:])
    return [p for p in out if p.strip()]


# What a property stands for: a formula with one name marked as its hole. This
# notation is never parsed from anything; it exists only inside a binding.
PROPERTY = 'property-of'


def binding_context(notations):
    """Which notations bind a variable, and which apply a property or a
    function.

    Both are read from the declarations: a binder is a notation with a `binds`
    line, and an application is one whose first hole takes a property or a
    function. `props` says which of the two each applies, because a function
    is read as a family only where a binder applies it to what it binds.
    Nothing here is known by name.
    """
    binders, props = {}, {}
    for n in notations:
        if n.holes and n.holes[0] in ('property', 'function'):
            props[n.stands_under or n.name] = n.holes[0]
        if n.binds:
            binders[n.stands_under or n.name] = n.binds
    return binders, props


def binding_sites(pattern, binders, props, bound=(), out=None):
    """The occurrences of a property that may decide what it stands for.

    Only one may: the occurrence inside the braces, applied to the very
    variable the braces bind. There the answer is forced, because a property is
    introduced before the braces open and so cannot mention what they bind, and
    every occurrence of that variable in the condition must therefore be the
    hole. An occurrence outside is applied to an ordinary name the property is
    allowed to mention, where several readings would fit, so it is checked
    against what the inside one decided and never allowed to decide.
    """
    out = set() if out is None else out
    if (pattern.notation in props and len(pattern.children) == 2
            and pattern.children[1].notation == 'name'
            and pattern.children[1].text in bound):
        out.add(id(pattern))
    held, body = binders.get(pattern.notation, ((), ()))
    own = tuple(pattern.children[at].text for at in held
                if pattern.children[at].notation == 'name')
    for i, child in enumerate(pattern.children):
        inner = (*bound, *own) if i in body else bound
        binding_sites(child, binders, props, inner, out)
    return out


def equations(records):
    """The notations that are equations, taken from what they target in the
    kernel, `wceq`, rather than named here. An equation's two sides say the
    same read either way round (`SYNTAX.md`).
    """
    return {r.name for r in records if r.kind == 'notation'
            and re.match(r'wceq\b', r.fields.get('metamath', '').strip())}


def orders(a, b, equations):
    """The ways b's parts may stand against a's: as written, and turned
    round where a is an equation.
    """
    if a.notation in equations and len(b.children) == 2:
        return [b.children, b.children[::-1]]
    return [b.children]


def match(pattern, ground, binding, variables, props, sites, binders,
          equations):
    """Bind the pattern's variables so that it becomes the ground tree.

    Returns the binding, or None. The binding is not modified on failure.
    `props` and `binders` are `binding_context`'s, and `equations` the
    notations `equations` gives. Two trees are compared up to the letters
    they bind and the order of an equation's sides (`alike`), and a binder
    of the pattern's may take the ground's letter (`_bound_as`).
    """
    if pattern.notation == 'name' and pattern.text in variables:
        seen = binding.get(pattern.text)
        if seen is not None:
            return (binding if alike(seen, ground, binders, equations)
                    else None)
        out = dict(binding)
        out[pattern.text] = ground
        return out
    if (pattern.notation in props and len(pattern.children) == 2
            and pattern.children[0].notation == 'name'
            and pattern.children[0].text in variables):
        if props.get(pattern.notation) != 'function':
            return _property(pattern, ground, binding, sites, binders,
                             equations)
        decides, found = _family(pattern, ground, binding, sites, binders,
                                 equations)
        if decides:
            return found
    if pattern.notation != ground.notation or pattern.text != ground.text:
        return None
    if len(pattern.children) != len(ground.children):
        return None
    pattern = _bound_as(pattern, ground, variables, binders)
    for children in orders(pattern, ground, equations):
        found = binding
        for a, b in zip(pattern.children, children, strict=True):
            found = match(a, b, found, variables, props, sites, binders,
                          equations)
            if found is None:
                break
        if found is not None:
            return found
    return None


def _bound_as(pattern, ground, variables, binders):
    """The pattern with the letter it binds spelt as the ground spells it,
    where the letter is no variable of the pattern's and the ground's
    letter is free nowhere in it; the pattern as it is otherwise.

    A definition's formula read at a term binds a letter of its own, and a
    line saying the same thing may bind another: `there is b ∈ G with
    gH = bH` answers K's `there is g ∈ G with X = gH` at X := gH.
    """
    held, body = binders.get(pattern.notation, ((), ()))
    for at in held:
        ours, theirs = pattern.children[at], ground.children[at]
        if (ours.notation != 'name' or theirs.notation != 'name'
                or ours.text == theirs.text or ours.text in variables
                or theirs.text in pattern.names()):
            continue
        pattern = Node(pattern.notation, pattern.sort,
                       [theirs if i == at
                        else substitute(c, {ours.text: theirs}) if i in body
                        else c
                        for i, c in enumerate(pattern.children)], pattern.text)
    return pattern


def alike(a, b, binders, equations, ours=None, theirs=None):
    """Whether two trees are one formula, spelt alike but for the letters
    they bind: `there is a ∈ G with Z = aH` and `there is b ∈ G with
    Z = bH` are one claim, and neither says anything of a or of b.

    `binders` is `binding_context`'s. A letter one of them binds is paired
    with the letter the other binds in the same place, and a free letter
    must be the same letter on both sides, never one the other side binds.
    An equation is alike either way round (`orders`).
    """
    ours, theirs = ours or {}, theirs or {}
    if a.notation == 'name' and b.notation == 'name':
        if a.text in ours or b.text in theirs:
            return ours.get(a.text) == b.text and theirs.get(b.text) == a.text
        return a.text == b.text
    if (a.notation != b.notation or a.text != b.text
            or len(a.children) != len(b.children)):
        return False
    shape = binders.get(a.notation)
    if shape is None:
        return any(all(alike(x, y, binders, equations, ours, theirs)
                       for x, y in zip(a.children, kids, strict=True))
                   for kids in orders(a, b, equations))
    held, body = shape
    pairs = [(a.children[at], b.children[at]) for at in held]
    if any(x.notation != 'name' or y.notation != 'name' for x, y in pairs):
        return a.shape() == b.shape()
    inner = ({**ours, **{x.text: y.text for x, y in pairs}},
             {**theirs, **{y.text: x.text for x, y in pairs}})
    return all(i in held or alike(p, q, binders, equations,
                                *(inner if i in body else (ours, theirs)))
               for i, (p, q) in enumerate(zip(a.children, b.children,
                                              strict=True)))


def _property(pattern, ground, binding, sites, binders, equations):
    """P applied to something, where P is one of the pattern's variables."""
    name, arg = pattern.children[0].text, _read_at(pattern.children[1],
                                                   binding)
    if name not in binding:
        if id(pattern) not in sites or arg.notation != 'name':
            return None                 # only the inside occurrence decides
        out = dict(binding)
        out[name] = Node(PROPERTY, 'property', [ground], arg.text)
        return out
    stands = binding[name]
    if stands.notation != PROPERTY:
        return None
    filled = substitute_apart(stands.children[0], {stands.text: arg}, binders)
    return binding if alike(filled, ground, binders, equations) else None


def _read_at(arg, binding):
    """What a property or a function is applied to, in the ground's terms.

    Every name in it the match has bound is what it was bound to: an item's
    `t(n + 1)` asks of the step's summand at m + 1 where n is m, and its
    `t(k − c)` at k − 1 where c is 1. What is bound to a property is not a
    term, and is left alone.
    """
    return substitute(arg, {v: t for v, t in binding.items()
                            if t.notation != PROPERTY})


def _family(pattern, ground, binding, sites, binders, equations):
    """t applied to something, where t is a function the pattern names.

    Under a binder that applies it to what it binds, t is whatever is summed
    or said there, read as a term with that variable as its hole: an item
    summing t(k) over k is about d(k)·10^k − d(k) when that is the step's
    summand. It is read so only where the term is not itself a function
    applied to the variable, since there t is simply that function, and the
    item's other mentions of t, which are not applications, still name it.

    Gives back whether this decides the match, and the binding it decides on
    or None where it refuses. Where it does not decide, the application is
    matched as it stands.
    """
    name, arg = pattern.children[0].text, _read_at(pattern.children[1],
                                                   binding)
    stands = binding.get(name)
    if stands is not None and stands.notation == PROPERTY:
        filled = substitute_apart(stands.children[0], {stands.text: arg},
                                  binders)
        return True, (binding if alike(filled, ground, binders, equations)
                      else None)
    plain = (ground.notation == pattern.notation and len(ground.children) == 2
             and ground.children[1].shape() == arg.shape())
    if (stands is None and id(pattern) in sites and arg.notation == 'name'
            and not plain):
        out = dict(binding)
        out[name] = Node(PROPERTY, 'property', [ground], arg.text)
        return True, out
    return False, None


class Rule:
    """What a define with an argument stands for: `define S(m) := …` is a
    function, and S(t) is its body with t for m.
    """

    def __init__(self, param, body, domain=None):
        self.param, self.body, self.domain = param, body, domain


def expand(node, definitions, depth=8):
    """The tree with every defined name replaced by the term it names.

    A define abbreviates and asserts nothing, so the two are one formula when
    two formulas are compared: a step claiming `𝒫X = U ∪ T` and a theorem
    concluding the same thing with the sets written out say the same thing. A
    define may be written in terms of an earlier one, so this repeats, and the
    depth is bounded because nothing stops a file naming something after
    itself.

    A defined function is read where it is applied: S(k + 1) is the rule
    with k + 1 for its parameter. Standing alone it is the function, and
    stays a name.
    """
    if not definitions or depth <= 0:
        return node
    if node.notation == 'name' and node.text in definitions:
        found = definitions[node.text]
        if isinstance(found, Rule):
            return node
        return expand(found, definitions, depth - 1)
    if node.notation == 'application' and len(node.children) == 2 \
            and node.children[0].notation == 'name' \
            and isinstance(definitions.get(node.children[0].text), Rule):
        rule = definitions[node.children[0].text]
        at = expand(node.children[1], definitions, depth)
        return expand(substitute(rule.body, {rule.param: at}), definitions,
                      depth - 1)
    if not node.children:
        return node
    return Node(node.notation, node.sort,
                [expand(c, definitions, depth) for c in node.children],
                node.text)


def substitute(node, binding):
    """The tree with each bound name replaced by what it stands for."""
    if node.notation in ('name', 'numeral'):
        return binding.get(node.text, node)
    return Node(node.notation, node.sort,
                [substitute(c, binding) for c in node.children], node.text)


# Letters a binder is renamed to, where a value put under it would be caught.
FRESH = [*'abcdefghijklmnopqrstuvwxyz', *(f"{c}'" for c in
                                          'abcdefghijklmnopqrstuvwxyz')]


def substitute_apart(node, binding, binders):
    """`substitute`, keeping what a binder binds apart from what is put
    under it: K's `there is g ∈ G with X = gH` at X := gH is `there is
    a ∈ G with gH = aH`, and never `there is g ∈ G with gH = gH`, which
    catches the g of gH and says something else. A binder whose letter a
    value mentions is spelt with a letter nothing there uses; one naming a
    letter the binding replaces keeps it, as the letter is its own inside.
    """
    if node.notation in ('name', 'numeral'):
        return binding.get(node.text, node)
    held, body = binders.get(node.notation, ((), ()))
    if not held or any(node.children[at].notation != 'name' for at in held):
        return Node(node.notation, node.sort,
                    [substitute_apart(c, binding, binders)
                     for c in node.children], node.text)
    own = {node.children[at].text for at in held}
    inner = {k: v for k, v in binding.items() if k not in own}
    used = node.names().union(*(v.names() for v in binding.values()))
    spelt, renamed = {}, dict(inner)
    for at in held:
        var = node.children[at]
        if any(var.text in v.names() for v in inner.values()):
            fresh = Node('name', var.sort, [], next(c for c in FRESH
                                                    if c not in used))
            used.add(fresh.text)
            spelt[at], renamed[var.text] = fresh, fresh
    return Node(node.notation, node.sort,
                [spelt.get(i, c) if i in held
                 else substitute_apart(c, renamed, binders) if i in body
                 else substitute_apart(c, binding, binders)
                 for i, c in enumerate(node.children)], node.text)
