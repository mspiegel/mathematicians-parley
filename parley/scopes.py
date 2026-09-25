"""Scopes: the context each line of a proof is proved under.

This is the second of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). Given the blocks, hypotheses, cases and `define` lines,
it produces the context each line is proved under, carries a fact into an
inner scope, and closes a block into the claim it owns. This is working in
deduction form, and the section on scopes in `ELABORATION.md` describes it.
"""


class Fact:
    """A claim, a proof of it at one scope, and the sentences it was read from.

    A line may say several things, and a substitution may land in one of
    them, so what is kept is every sentence rather than the claim as one
    tree. A line read from no text at all keeps none.
    """

    def __init__(self, term, proof, sentences=()):
        self.term, self.proof, self.sentences = term, proof, sentences


class Block:
    """A block being elaborated: what it opened over and what it opened."""

    def __init__(self, owner, outer, facts, frame):
        self.owner, self.outer, self.outside = owner, outer, facts
        self.frame = frame          # index into the scope frames
        self.scope, self.facts = outer, facts
        self.supposed = None        # contradiction
        self.over = self.base = None                      # induction
        self.variable = None        # the setvar a fix introduced
        self.named = None           # the names in hand before it opened
        self.bound = None           # and which variable each binder had
        self.inner = None           # and which each had while it was open
        self.assumed = {}           # cases: part number -> what it assumes
        self.entered = None         # cases: the part now open
        self.case_opened_at = None  # cases: the closers before that part
        self.claim = self.proof = None
        self.parts = {}             # part number -> the last fact in it
