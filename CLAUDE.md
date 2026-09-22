# Working in this repository

## Exceptions

**An exception may not be used as control flow.** A route that does not apply, a
lemma that does not fit, a pattern that does not match, a parse with no reading:
none of those is a failure. They are the ordinary course of a run where nothing
has gone wrong, and what they give back is a value.

Two types in `parley/parse.py` carry the distinction, and their docstrings hold
the reasoning rather than this file.

- `Problem` means a defect somebody has to fix — the proof text says something
  wrong, or a database record does. It is raised, and nothing carries on past it.
- `Declined` means a route asked whether it applies and the answer was no. It is
  returned, and `parse.declined` is what a caller asks.

Catching a `Problem` to try something else is accepting a proof with a defect in
it. An `except` here should name a `Problem`, a bad byte, or a missing file; if
what you are reaching for is a handler that catches and then tries another way,
the thing you want is a `Declined`.

Do not reach for `None` to say a route declined. `elaborate.py` returns None at
dozens of sites and already means several things by it, so one more meaning moves
the double duty rather than ends it; and `spell.seq` drops what is falsy, so a
decline arriving there as None would shorten a proof and say nothing whatever.
A `Declined` is truthy and is not a string, which is what makes a caller who
forgot to look raise at the line that forgot.

The test is whether the raise can happen on a run where nothing is wrong. If it
fires hundreds of times in a green build, it is branching and it is spelt wrong.
