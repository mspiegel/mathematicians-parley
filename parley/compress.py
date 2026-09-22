"""Set.mm's compressed proof format, which writes a repeated subproof once.

A proof in normal format is a flat run of labels, and a subproof used twice
is written out twice. The corpus does that a great deal: in deduction form
every line carries the whole scope as an antecedent, so the same membership
is re-proved under the same scope wherever it is wanted.
`thm:least-combination-divides` step 3 writes `( under -> 1 e. NN0 )` six
hundred and nineteen times, and its scope — a hundred and twenty-eight
tokens — seven thousand four hundred and sixty-seven times.

The compressed format is what set.mm itself is stored in, and it says the
same proof with a way to point back. A step marked `Z` is kept, and a later
step that would repeat it names it instead. Nothing about the proof changes
and no verifier has to be told: `mmverify.py` reads both formats and the
same theorem comes out.

What is kept is decided by counting. A subproof that stands in more than
one place is worth a name; one that stands in a single place is not, and a
subproof of one token is never worth it, since naming it costs as much as
writing it again.

Indices are written in the format's own base: twenty values in `A` to `T`
for the last digit, and a bijective base five in `U` to `Y` above it. The
first indices are the theorem's own hypotheses, in the order the database
declares them; then the labels named in the parentheses; then, past those,
the steps that were kept.
"""
LAST ='ABCDEFGHIJKLMNOPQRST'      # 0 to 19: the last digit of an index
HIGH = 'UVWXY'                     # 1 to 5: the digits above it


def letters(index):
    """One index, written the way the format reads it."""
    high, last = divmod(index, 20)
    out = []
    while high:
        high, digit = divmod(high - 1, 5)
        out.append(HIGH[digit])
    return ''.join(reversed(out)) + LAST[last]


def shapes(proof, sigs):
    """Every subproof of a proof, numbered so that two alike share a number.

    A label is applied to what its hypotheses ask for, so the run can be
    read back into a tree with one pass and a stack. Two subproofs that are
    the same run of labels are the same subproof, and giving them one
    number here is what lets the rest of this work on numbers rather than
    on the text: the step being counted is four and a half million tokens
    long in one case, and comparing those as strings is the quadratic this
    avoids."""
    seen, kinds, stack = {}, [], []
    for token in proof.split():
        sig = sigs[token]
        count = len(sig.floats) + len(sig.essentials)
        kids = tuple(stack[len(stack) - count:]) if count else ()
        del stack[len(stack) - count:]
        key = (token, kids)
        at = seen.get(key)
        if at is None:
            at = seen[key] = len(kinds)
            kinds.append(key)
        stack.append(at)
    if len(stack) != 1:
        raise ValueError(f'the proof leaves {len(stack)} things on the stack')
    return stack[0], kinds


def standing(root, kinds):
    """How many places each subproof stands in, counted no higher than two.

    Two is all the decision needs, and the true count is past counting: a
    proof that shares its parts all the way down stands for a tree with
    more nodes than it has tokens, by a lot. A subproof is numbered after
    everything it holds, so one pass from the top down reaches each before
    the things under it."""
    out = [0] * len(kinds)
    out[root] = 1
    for at in range(len(kinds) - 1, -1, -1):
        if out[at]:
            for kid in kinds[at][1]:
                out[kid] = min(out[kid] + out[at], 2)
    return out


def compress(proof, mandatory, sigs):
    """One proof in normal format, said in the compressed one."""
    root, kinds = shapes(proof, sigs)
    often = standing(root, kinds)
    worth = [n for n, (_token, kids) in enumerate(kinds)
             if kids and often[n] > 1]

    # The labels the parentheses name, in the order they are first written.
    # A theorem's own hypotheses are not among them: they are the indices
    # below, and naming them again would shift everything.
    order, seen = [], set(mandatory)
    for token, _kids in kinds:
        if token not in seen:
            seen.add(token)
            order.append(token)
    index = {label: n for n, label in enumerate(mandatory)}
    for n, label in enumerate(order):
        index[label] = len(mandatory) + n
    past = len(mandatory) + len(order)

    # Written without recursion. These run to millions of steps and the
    # deepest is deeper than any stack Python will give.
    keeping, kept, out = dict.fromkeys(worth), {}, []
    work = [(root, False)]
    while work:
        at, done = work.pop()
        if done:
            out.append(letters(index[kinds[at][0]]))
            if at in keeping:
                kept[at] = len(kept)
                out.append('Z')
            continue
        if at in kept:
            out.append(letters(past + kept[at]))
            continue
        work.append((at, True))
        work.extend((kid, False) for kid in reversed(kinds[at][1]))
    return f'( {" ".join(order)} ) {"".join(out)}'


def expand(said, mandatory, sigs):
    """A compressed proof read back, for checking that it says the same.

    Nothing in the build needs this. `parley/test_compress.py` does: what
    makes a format change safe to make is that the proof it writes is the
    proof it was given, and this is how that is asked."""
    head, _, rest = said.partition(')')
    block = mandatory + head.replace('(', '').split()
    numbers, running = [], 0
    for letter in ''.join(rest.split()):
        if letter == 'Z':
            numbers.append(None)
        elif letter in LAST:
            numbers.append(20 * running + LAST.index(letter))
            running = 0
        else:
            running = 5 * running + HIGH.index(letter) + 1
    stack, saved = [], []
    for number in numbers:
        if number is None:
            saved.append(stack[-1])
        elif number < len(block):
            label = block[number]
            sig = sigs[label]
            count = len(sig.floats) + len(sig.essentials)
            args = stack[len(stack) - count:] if count else []
            del stack[len(stack) - count:]
            stack.append(' '.join([*args, label]))
        else:
            stack.append(saved[number - len(block)])
    return stack[0]
