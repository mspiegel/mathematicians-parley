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

# An instantiation value may itself contain a comma, as `e := gcd(a, b)` does,
# so the list is split at the commas that sit outside brackets rather than by a
# pattern that stops at the first one.
ASSIGN = re.compile(r'([^\s,]+)\s*:=\s*(.+)')


def instantiation(text):
    """The `v := t` pairs of a justification, in order."""
    body = re.split(r',\s*from\b|\s+in\s+(?:line\b|def:)', text, maxsplit=1)[0]
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


def match(pattern, ground, binding, variables):
    """Bind the pattern's variables so that it becomes the ground tree.

    Returns the binding, or None. The binding is not modified on failure."""
    if pattern.notation == 'name' and pattern.text in variables:
        seen = binding.get(pattern.text)
        if seen is not None:
            return binding if seen.shape() == ground.shape() else None
        out = dict(binding)
        out[pattern.text] = ground
        return out
    if pattern.notation != ground.notation or pattern.text != ground.text:
        return None
    if len(pattern.children) != len(ground.children):
        return None
    for a, b in zip(pattern.children, ground.children):
        binding = match(a, b, binding, variables)
        if binding is None:
            return None
    return binding


def names(node):
    """Every name the tree mentions."""
    if node.notation == 'name':
        return {node.text}
    return set().union(set(), *(names(c) for c in node.children))


def match_all(patterns, facts, binding, variables):
    """Match every pattern against a fact of its own, or return None.

    Each fact is used once, because two hypotheses asking the same thing want
    two lines saying it. The search backtracks, since an early pattern that
    fits several facts can bind a name the wrong way."""
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
    itself."""
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
