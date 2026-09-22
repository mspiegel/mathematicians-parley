"""Match an item's hypothesis against the fact a step supplies for it.

The match is one-way: the item is a pattern whose names stand for anything, and
the fact is ground. `thm:subset-transitive` assumes X ⊆ Y and Y ⊆ Z, and a step
citing it from two lines claiming S ⊆ [a, b] and [a, b] ⊆ ℝ supplies them with
X, Y, Z standing for S, [a, b] and ℝ. A name that appears twice must stand for
the same thing both times, which is what makes the middle Y load-bearing.

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
    """Which notations bind a variable, and which apply a property.

    Both are read from the declarations: a binder is a notation with a `binds`
    line, and a property application is one whose first hole takes a property.
    Nothing here is known by name.
    """
    binders, props = {}, set()
    for n in notations:
        if n.holes and n.holes[0] == 'property':
            props.add(n.stands_under or n.name)
        if not n.binds:
            continue
        holes = [int(x) - 1 for x in re.findall(r'hole[s]?\s+(\d+)', n.binds)]
        over = re.search(r'over\s+holes?\s+(\d+)(?:\s+and\s+(\d+))?', n.binds)
        if holes and over:
            body = [int(g) - 1 for g in over.groups() if g]
            binders[n.stands_under or n.name] = (holes[0], body)
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
    shape = binders.get(pattern.notation)
    for i, child in enumerate(pattern.children):
        inner = bound
        if shape and i in shape[1]:
            var = pattern.children[shape[0]]
            if var.notation == 'name':
                inner = (*bound, var.text)
        binding_sites(child, binders, props, inner, out)
    return out


def match(pattern, ground, binding, variables, props=(), sites=frozenset()):
    """Bind the pattern's variables so that it becomes the ground tree.

    Returns the binding, or None. The binding is not modified on failure.
    """
    if pattern.notation == 'name' and pattern.text in variables:
        seen = binding.get(pattern.text)
        if seen is not None:
            return binding if seen.shape() == ground.shape() else None
        out = dict(binding)
        out[pattern.text] = ground
        return out
    if (pattern.notation in props and len(pattern.children) == 2
            and pattern.children[0].notation == 'name'
            and pattern.children[0].text in variables):
        return _property(pattern, ground, binding, sites)
    if pattern.notation != ground.notation or pattern.text != ground.text:
        return None
    if len(pattern.children) != len(ground.children):
        return None
    for a, b in zip(pattern.children, ground.children, strict=True):
        binding = match(a, b, binding, variables, props, sites)
        if binding is None:
            return None
    return binding


def _property(pattern, ground, binding, sites):
    """P applied to something, where P is one of the pattern's variables."""
    name, arg = pattern.children[0].text, pattern.children[1]
    if arg.notation == 'name' and arg.text in binding:
        arg = binding[arg.text]
    if name not in binding:
        if id(pattern) not in sites or arg.notation != 'name':
            return None                 # only the inside occurrence decides
        out = dict(binding)
        out[name] = Node(PROPERTY, 'property', [ground], arg.text)
        return out
    stands = binding[name]
    if stands.notation != PROPERTY:
        return None
    filled = substitute(stands.children[0], {stands.text: arg})
    return binding if filled.shape() == ground.shape() else None


def names(node):
    """Every name the tree mentions."""
    if node.notation == 'name':
        return {node.text}
    return set().union(set(), *(names(c) for c in node.children))


def match_all(patterns, facts, binding, variables):
    """Match every pattern against a fact of its own, or return None.

    Each fact is used once, because two hypotheses asking the same thing want
    two lines saying it. The search backtracks, since an early pattern that
    fits several facts can bind a name the wrong way.
    """
    if not patterns:
        return binding
    first, rest = patterns[0], patterns[1:]
    for i, fact in enumerate(facts):
        found = match(first, fact, binding, variables)
        if found is None:
            continue
        done = match_all(rest, facts[:i] + facts[i + 1:], found, variables)
        if done is not None:
            return done
    return None


def expand(node, definitions, depth=8):
    """The tree with every defined name replaced by the term it names.

    A define abbreviates and asserts nothing, so the two are one formula when
    two formulas are compared: a step claiming `𝒫X = U ∪ T` and a theorem
    concluding the same thing with the sets written out say the same thing. A
    define may be written in terms of an earlier one, so this repeats, and the
    depth is bounded because nothing stops a file naming something after
    itself.
    """
    if not definitions or depth <= 0:
        return node
    if node.notation == 'name' and node.text in definitions:
        return expand(definitions[node.text], definitions, depth - 1)
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
