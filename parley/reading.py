"""Reading: a line of the page, as kernel terms.

This is the first of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). Given a line of the page and the notation records, it
produces kernel terms, with each name the page uses standing for a kernel
variable. The sections of `ELABORATION.md` on names and on the statement a
theorem becomes describe it.

What a name stands for is `names`, which the scopes change as blocks open and
close; which kernel variable a binder or a fixed name takes is decided here,
once, and kept in `bound_as`.
"""
import contextlib
import re

import kernel
import targets
from formula import Node, parse
from match import Rule, substitute
from parse import Theorem, cited_name, declined, define_parts, proved, resolve
from sorts import (
    definition_sorts,
    file_definitions,
    sorts_of_record,
    sorts_of_statement,
)

LABEL = re.compile(r'\s*\([A-Z]+[0-9]*\)\s*$')
# `let A be a set` introduces a name the way `let n ∈ ℕ` does, and states
# what `A is a set` states. The hypothesis line reads better as it is
# written; the claim is the notation the database declares. Points are the
# same shape, and every sort with a notation could be.
BE_A = re.compile(r'\s+be\s+a\s+(set|point)\b')
BE_AN_ELEMENT = re.compile(r'^(\S+)\s+be\s+an\s+element$')
NOT_IN = re.compile(r'^(\S+)\s*∉\s*\S')
CLASS_NAMES = ['cA', 'cB', 'cC', 'cD', 'cE', 'cF', 'cG', 'cH']


def hypothesis_body(kind, text):
    """What a hypothesis line claims, with its introduction read as one.

    `let A be a set` and `let P be a point` introduce a name and state what
    the sort means, and the notation that states it is what the database
    declares. The line reads better as it is written, so the substitution
    happens here and every reader of a hypothesis gets it.

    `let a ∉ X` and `let x be an element` claim no kind on the page, and the
    kernel still wants the thing to be a set, not a proper class: `{a}` of a
    proper class is empty. That sethood is apparatus (`READERS.md`, hidden
    entirely), so it is added here and never written: `let a ∉ X` reads as
    a is a set and a ∉ X, and `let x be an element` as x is a set.
    """
    body = text[len(kind):] if text.startswith(kind) else text
    if kind == 'let':
        said = LABEL.sub('', body).strip()
        element = BE_AN_ELEMENT.match(said)
        if element:
            return f'{element.group(1)} is a set'
        outside = NOT_IN.match(said)
        if outside:
            return f'{outside.group(1)} is a set and {said}'
        body = BE_A.sub(lambda m: f' is a {m.group(1)}', body)
    return body


def render(rpn, sigs):
    """A term written the way a Metamath file writes it.

    A proof is reverse Polish because that is what the kernel reads, and a
    `$a` states its claim in full, so anything the elaborator writes out has
    to come back the other way.
    """
    stack = []
    for token in rpn.split():
        sig = sigs[token]
        count = len(sig.floats)
        args = stack[len(stack) - count:] if count else []
        del stack[len(stack) - count:]
        bound = dict(zip(sig.push, args, strict=True))
        stack.append(' '.join(bound.get(t, t) for t in sig.statement[1:]))
    return stack[0]


class _Literal:
    """A term already in kernel form, standing in a tree."""
    notation, sort, children, text = 'literal', None, (), ''

    def __init__(self, term):
        self.term = term


class Reading:
    @contextlib.contextmanager
    def names_kept(self, sets=False):
        """What each name stands for, as it is now, given back afterwards.

        Reading a binder's body, a definition's right side, or an item cited
        at its instantiation binds names for as long as that reading lasts,
        and the proof's own meaning of each word comes back when it ends.
        What is given to the block is the meaning as it was. `sets`, what
        each name was let into, is given back too where asked.
        """
        saved = dict(self.names)
        kept = dict(self.sets) if sets else None
        try:
            yield saved
        finally:
            self.names = saved
            if sets:
                self.sets = kept

    @contextlib.contextmanager
    def in_its_names(self, item):
        """The sorts an item's own lines state, while its lines are read.

        A name is what says which of two notations sharing a pattern is
        meant, and `|_|` is cardinality or absolute value according to what
        stands inside it. The names in scope are the proof's; an item's
        hypotheses are written in its own, and `let Y be a set` is where it
        says so.

        A theorem of the corpus is read in its own file's definitions too,
        written out: its T is its file's T, whatever the citing proof calls
        T or whether it has one.
        """
        kept, kept_written = self.g.sorts, self.from_outside
        written = (file_definitions(item, self.g)
                   if isinstance(item, Theorem) else {})
        own = (sorts_of_statement(item) if isinstance(item, Theorem)
               else sorts_of_record(item, self.g))
        self.g.sorts = {**kept, **definition_sorts(written), **own}
        self.from_outside = written
        try:
            yield
        finally:
            self.g.sorts, self.from_outside = kept, kept_written

    def read(self, text):
        """One sentence of the readable layer, as a tree.

        Where the elaborator has got to goes with it. A formula that does
        not parse is a defect and wants somewhere to point; without a
        position it arrived looking like a route declining, and a `requires`
        line nobody could read was taken as stated instead of reported.
        """
        return parse(LABEL.sub('', text).strip(), self.g,
                     self.thm.path, self.at)

    def term(self, node):
        if node.notation == 'literal':
            return node.term
        # A statement is read with the definitions from outside its theorem
        # written out, so what it says in set.mm never names them and a
        # theorem citing it needs none of them (`from_outside`).
        written = self.from_outside.get(node.children[0].text) \
            if self.from_outside and node.notation == 'application' \
            and len(node.children) == 2 \
            and node.children[0].notation == 'name' else None
        if isinstance(written, Rule):
            return self.term(substitute(written.body,
                                        {written.param: node.children[1]}))
        if node.notation == 'name' and node.text in self.from_outside \
                and not isinstance(self.from_outside[node.text], Rule):
            return self.term(self.from_outside[node.text])
        if node.notation == 'name':
            if node.text not in self.names:
                # A name the proof never introduced, which is the text's to
                # fix wherever the reading of it came from.
                raise self.defect(self.at,
                                  f'no kernel name for {node.text!r}')
            return self.names[node.text]
        if node.notation == 'numeral':
            # set.mm writes a numeral of several digits as decimals, `; A B`
            # with A the digits before the last: 10 is `; 1 0`.
            said = targets.NUMERALS[node.text[0]]
            for digit in node.text[1:]:
                said = self.seq(said, targets.NUMERALS[digit], 'cdc')
            return said
        # A binder's first hole is the variable it introduces, which stands
        # for itself rather than for whatever a name is bound to.
        bound = self.binders.get(node.notation, ())
        with self.names_kept():
            for i in bound:
                # The body speaks of what the binder introduces, so the name
                # stands for its own variable while the body is read.
                said = node.children[i].text
                self.names[said] = f'{self.binder_var(said)} cv'
            holes = [self.binder_var(c.text) if i in bound else self.term(c)
                     for i, c in enumerate(node.children)]
        return targets.fill(self.pattern(node), holes)

    def pattern(self, node):
        """The `target` entry of the pattern this node was built from.

        A notation with no target is a gap in `db/notation.records` and so
        a person's to fix. The position is the line that wrote the notation
        rather than the record that fails to declare it, because that is the
        one this knows and it is where a reader would start looking.
        """
        entries = self.terms.get(node.notation)
        if entries is None:
            raise self.defect(self.at,
                              f'notation {node.notation!r} has no target field')
        order = self.literals.get(node.notation, [])
        found = entries[order.index(node.text)] if node.text in order \
            else entries[0]
        if found is None:
            raise self.defect(self.at,
                              f'notation {node.notation!r} builds no term here')
        return found

    def to_term(self, rpn):
        """A term the proof holds, read back as a tree."""
        stack = []
        for token in rpn.split():
            sig = self.sigs[token]
            if sig.kind == '$f':
                stack.append(kernel.Term(variable=sig.statement[1]))
                continue
            count = len(sig.floats)
            args = stack[len(stack) - count:] if count else []
            del stack[len(stack) - count:]
            stack.append(kernel.Term(token, tuple(args)))
        return stack[0]

    def item_cited(self, cited):
        """The item a citation in this theorem's file names.

        The citation is `def:x` or `thm:x`, spelt with its file's path, or
        bare for a theorem of this file.
        """
        return self.items[resolve(cited_name(cited), self.thm.module)]

    def flip(self, node):
        """The same equality with its sides the other way round."""
        return Node(node.notation, node.sort, list(reversed(node.children)),
                    node.text)

    def definition(self, name, subject, var=None):
        """A definition's right side, as nodes, with its names bound.

        Returns the unfolding lemma, the bound variable, the node the
        existential quantifies, and what it quantifies over. The body is
        returned facing the way the lemma writes it, which is not always the
        way the text writes it.
        """
        item = self.item_cited(name)
        lemma, flipped = targets.unfolding(item)
        if lemma is None:
            raise self.defect(self.at,
                              f'{name} has no target field')
        var = var or self.flabel[self.sigs[lemma].bound()]
        node = self.read(item.conclusions[0][0])
        left, right = node.children
        self.names[self.subject_of(left).text] = subject
        self.names[right.children[0].text] = f'{var} cv'
        body = right.children[2]
        return (lemma, var, self.flip(body) if flipped else body, body,
                self.term(right.children[1]), self.term(left))

    def subject_given(self, name, pairs, line):
        """What the step writes for the letter a definition is about, found
        by that letter's name among its `v := t` pairs (`SYNTAX.md`: a
        substitution names its variable). `divides` is about d, and
        `n := c, d := d` gives d as d whichever pair comes first. A step that
        gives the subject no value is refused: the pair is not optional.
        """
        item = self.item_cited(name)
        left = self.read(item.conclusions[0][0]).children[0]
        letter = self.subject_of(left).text
        given = dict(pairs).get(letter)
        if given is None:
            raise self.defect(line, f'{name} is about {letter}, and the step '
                                    f'gives {letter} no value; write it, as '
                                    f'{letter} := t')
        return given

    def sentences(self, text):
        out = []
        for piece in LABEL.sub('', text).strip().split('. '):
            piece = piece.strip().rstrip('.').strip()
            if piece:
                out.append(piece)
        return out

    def claim_of(self, text):
        """A claim of several sentences is their conjunction.

        `then x ≤ |x|. −x ≤ |x|.` states two things at once, and the kernel
        has one conclusion, so the sentences are conjoined in the order the
        text writes them.
        """
        said = [self.term(self.read(s)) for s in self.sentences(text)]
        whole = said[0]
        for extra in said[1:]:
            whole = self.seq(whole, extra, 'wa')
        return whole

    def hypotheses(self):
        """Name every `let` variable, and read the hypotheses.

        A `let` introduces a name and says what it ranges over. `let n ∈ ℕ`
        says it with a membership, `let A be a set` with no set at all, and
        `let f : A → 𝒫A` by saying what the name maps between. All three
        name the thing they introduce first, so all three are read the same
        way: name the leftmost leaf, then read the line as a claim about
        it.
        """
        nodes, spare = [], list(CLASS_NAMES)
        for kind, text, _label, _line in self.thm.hypotheses:
            node = self.read(hypothesis_body(kind, text))
            if kind == 'let':
                introduced = self.subject_of(node)
                if introduced.text and introduced.text not in self.names:
                    self.names[introduced.text] = spare.pop(0)
                if node.notation == 'membership':
                    self.sets[introduced.text] = self.term(node.children[1])
            nodes.append(node)
        return nodes

    def defined(self, before):
        """Each `define` above line `before`, as its label, its line, the
        name it introduces and the term that name stands for.

        What the name becomes is the scopes part's (`define`): a variable
        of its own and the equation saying what it is. Here is only what
        the text says, read with the names in hand when it is reached, so
        each is taken before the next is read.

        It is read where it stands, which is what the parser's own comment
        says of it. One written above the first step names what the theorem
        fixes and is in hand before anything else; one written inside a
        block names what the block introduced, and the subsets proof has
        two of those, eighteen columns in, over an X a `fix` fixed and an
        `a` an `obtain` obtained. Read at the top they find neither.

        A block gives its names back when it closes, and these go with
        them.

        A function stands for the map from its domain to its rule, which
        is what set.mm has a function be: `define S(m) := Σ(j = 1 to m) j,
        for m ∈ ℕ` is the map sending each m ∈ ℕ to that sum.
        """
        # What the theorem sees from outside it comes first, before its own
        # first step: written out where it was defined, and from here on a
        # name like any the theorem defines itself.
        if not self.file_given:
            self.file_given = True
            written = file_definitions(self.thm, self.g)
            for name, d, src in self.visible_outside():
                if name in written:
                    yield (self.outside_label(name, d, src),
                           d[3] if src is self.thm.scope else self.thm.line,
                           name, self.outside_term(written[name]))
        while self.unread < len(self.thm.defines):
            _kind, text, label, line = self.thm.defines[self.unread]
            if line >= before:
                return
            self.unread += 1
            said = define_parts(text)
            if declined(said):
                raise self.defect(line, f'define {label}: {said}')
            if said.name in self.names:
                raise self.defect(line, f'{said.name} is already named')
            body = (said.body if said.param is None else
                    f'the map sending {said.param} ∈ {said.domain} '
                    f'to {said.body}')
            yield label, line, said.name, self.apart(
                self.term(self.read(body)))

    def visible_outside(self):
        """(name, define, scope) for each definition the theorem sees from
        outside it: those its file writes above it and those it imports.
        """
        scope = self.thm.scope
        return scope.visible(self.thm.line) if scope is not None else []

    def outside_label(self, name, d, src):
        """The label a definition from outside the theorem is held under:
        its own where its file is this theorem's, and the label on the
        import where it is imported, so a step cites it as the page does.
        """
        return (d[2] if src is self.thm.scope
                else self.thm.scope.import_label(name))

    def outside_term(self, made):
        """A definition from outside the theorem, written out, as a term:
        its rule, or for a function the map from its domain to its rule.
        """
        if not isinstance(made, Rule):
            return self.apart(self.term(made))
        var = self.binder_var(made.param)
        with self.names_kept():
            self.names[made.param] = f'{var} cv'
            body = self.term(made.body)
            over = self.term(self.read(made.domain))
        return self.apart(self.seq(var, over, body, 'cmpt'))

    def apart(self, rpn):
        """A term whose bound names are ones nothing else is using.

        A `define` names a thing by a body that binds a name of its own,
        and the proof may go on to fix a name spelt the same way: Cantor's
        B collects the x that its own image leaves out, and then fixes an x
        to reason about. Those are two names, and the kernel has to see two
        or the lemma that generalises over one will find the other.

        Only the names the body binds. A body may also mention a name the
        proof is already holding — the subsets proof defines U as the power
        set of X without the `a` it obtained — and renaming that one would
        make the definition speak of some other element.
        """
        whole = self.to_term(rpn)
        binding = {}
        holds = {t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
        for said in sorted(whole.names()):
            label = self.flabel.get(said)
            if label and label not in holds \
                    and self.sigs[label].statement[0] == 'setvar':
                fresh = self.spare_var()
                binding[said] = kernel.Term(
                    variable=self.sigs[fresh].statement[1])
        return whole.substitute(binding).rpn(self.flabel)

    def said(self, step):
        """Every sentence of a step's claim, as trees.

        `node` above is the last of them, because that is what an expansion
        is about. A line is cited whole, so what it keeps is all of them.
        """
        return tuple(self.read(s)
                     for s in self.sentences(' '.join(step.claim)))

    def render(self, rpn):
        """A term written the way a Metamath file writes it."""
        return render(rpn, self.sigs)

    def claimed_by(self, item):
        """What an item claims, from wherever its statement lives.

        A theorem the corpus proves is its proof, and the statement is at the
        head of it; one the library states has it in its record.
        """
        if proved(item):
            return item.conclusion
        return item.conclusions[0][0]

    def binder_var(self, name):
        """The setvar a binder's name stands for.

        A name is a letter and set.mm may have declared that letter as a
        class: Cantor quantifies over B, and B there is a class variable.
        So the letter's own label is taken only when it names a setvar, and
        a spare stands in otherwise — the same one every time, since the
        name is one name wherever the proof writes it.
        """
        if name in self.bound_as:
            return self.bound_as[name]
        label = self.flabel.get(name)
        if not (label and self.sigs[label].statement[0] == 'setvar'):
            label = self.spare_var()
        self.bound_as[name] = label
        self.written_as[label] = name
        return label

    def fixed_var(self, name, scope=''):
        """The variable a fixed name takes.

        Its own letter where nothing else is holding it, because the claim
        the block states binds that letter and the two have to agree: the
        `fix` in Cantor introduces the x that `for every x ∈ A` quantifies.
        A spare otherwise, as when a notation already binds the letter, or
        when set.mm declares the letter a class — the subsets proof fixes
        an X, and X there is a class variable.

        Agreement is why the answer is kept where a binder's is: the claim
        reads its quantifier through `binder_var`, and within the block the
        two are one binding.

        Kept, and not read. A name a block fixes is that block's, whatever
        the scope already binds by the same word: the subsets proof assumes
        `for every set X` and then fixes an X, and instantiating that
        assumption at a term about the fixed one would capture it if the
        two were one variable. So what the scope holds is avoided, and
        `close_block` gives the word back when the block ends.

        What the scope does not hold is free to agree, which is why the
        Cantor proof's fixed x is the x its conclusion quantifies.
        """
        own = self.flabel.get(name)
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | {t for t in scope.split()
                   if t in self.sigs and self.sigs[t].kind == '$f'})
        if not (own and self.sigs[own].statement[0] == 'setvar'
                and own not in held and own not in self.taken):
            own = self.spare_var()
        self.bound_as[name] = own
        self.written_as[own] = name
        return own

    def spare_var(self):
        """A kernel variable no name in this proof is already standing for.

        The names a proof introduces do not all come from here: the first
        `obtain` takes its variables from the existential the item states, so
        a later step asking for a spare can be handed one of them.

        What a name stands for now is not all of it. A binder's name stands
        for its variable only while its body is read, and `bound_as` is
        what says so for the rest of the proof. Bezout defines S over an m
        before any step writes one; handing that m out again would make one
        variable of two binders, and a lemma eliminating either of them
        forbids the other in what it carries.

        Running out is raised, not declined: it is the tool at its limit, a
        proof introducing more names than the kernel has letters, and not a
        route that does not apply. A decline here would go into an f-string
        as its message and stand in the proof as a kernel name.
        """
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | self.reserved | set(self.bound_as.values()))
        while self.spare and self.spare[0] in held:
            self.spare.pop(0)
        if not self.spare:
            raise self.defect(self.at,
                              'no variable left to introduce a name with')
        return self.spare.pop(0)

    def freeze(self, node):
        """The tree with its leaves turned into the terms they stand for.

        A definition's body is read with the definition's own names bound,
        and those names may be the ones the proof is using for something
        else: `def:stdlib/divisibility/odd` binds `k` and so does the step that
        obtains from it. Freezing the tree settles what it means before the names change
        back. A binder's own variable is left alone: it stands for itself,
        and the slot it fills wants the variable rather than a term saying
        what the variable means.
        """
        if not node.children:
            return _Literal(self.term(node))
        # The body speaks of what the binder introduces, so the name stands
        # for its own variable while the body is frozen, exactly as `term`
        # does it. Without this the body's leaves are read against whatever
        # the proof happens to be holding, which is nothing once the block
        # that fixed a name of the same spelling has closed.
        bound = self.binders.get(node.notation, ())
        with self.names_kept():
            for i in bound:
                said = node.children[i].text
                self.names[said] = f'{self.binder_var(said)} cv'
            return Node(node.notation, node.sort,
                        [c if i in bound else self.freeze(c)
                         for i, c in enumerate(node.children)], node.text)

    def substituted(self, node, old, new):
        """The node with one name replaced, for reading off the instance."""
        if self.term(node) == old:
            return _Literal(new)
        if not node.children:
            return node
        return Node(node.notation, node.sort,
                    [self.substituted(c, old, new) for c in node.children],
                    node.text)
