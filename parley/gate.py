#!/usr/bin/env python3
"""Everything that must be green before a commit, after `parley/build.py`.

Build first, every time. Nothing here runs the elaborator over the corpus:
the last stage verifies the files the elaborator *has written*, so it says
something about the corpus as it stands only if those files were written from
it. Break the elaborator, leave the built files alone, and all eleven stages
pass while no proof elaborates at all. `build.py` is what compares the two —
it says `84 built, 0 changed` — and the gate is what checks the result.

Eleven things: the lint settings in `ruff.toml`, that no caller hands on a
decline without asking whether it has one, the planted shapes that prove
that stage still finds them, the checker over the whole corpus, the planted
defects that prove the checker still catches things, the planted defects that
prove the elaborator still reports things, every set.mm label the database
names, that every library item is cited by a proof or has a test in
`tests/stdlib/`, that a compressed proof is the proof it was made from, that
no elaborated proof or test takes a step as stated that `ELABORATION.md` does
not record, and a verifier over every proof the elaborator has written. Any
one of them failing fails the gate.

The first three read the tools; the rest read the corpus. The last is the
only one that is evidence the elaborator is right rather than
consistent. The seven before it read the corpus against itself or against a
list of names. A proof that assumes nothing and proves the wrong thing would
pass all of them, and one already has.

The eighth is there because an item's statement is written by hand beside
the lemma it names, and only a citation that elaborates asks whether the two
agree. The tenth is there because a step taken as stated verifies: the
verifier reads it as an axiom, so the last stage cannot see one, and a list
in the file's header is read by nobody.

The sixth is there because none of the others watches what the elaborator
does with a defect. It may take a step as stated where it has no method for
it, which is right, and it did the same where the text was wrong, which is
not: the step was listed as assumed and the error never seen. Nothing said
so, because the file it wrote verified.

They run at once. Every one of them reads the corpus and none of them writes
it: the two that plant a defect copy what they edit into a directory of
their own first, which is what makes that true and is why they were written
that way. What they share is the machine, and four of them read set.mm:
`mmverify.py` peaks above a gigabyte doing it, so they are held to `WORKERS`
at a time rather than started together. What is said about each waits until
it is finished and is then printed in the order listed here, because a gate
whose output arrives interleaved is a gate nobody reads.

Serially this took fifty-four seconds and now takes twenty, which is what
the longest stage takes. That stage is the one running `mmverify.py`, and
nearly all of what it costs is reading set.mm: given a file whose whole
contents are `$[ set.mm $]` it takes seventeen and a half seconds, and the
proofs add a tenth of one. It is not vendored and so has no cache to
give it, which puts a floor under the gate that nothing here can lift.

Three of them need something this repository does not carry, and none of the
three is vendored. ruff: if it is missing, say

    pip install ruff

or run it from a virtual environment, and the gate looks for it on PATH.
set.mm is 51 MB and belongs to metamath, so it is not committed either; say
where it is with `SET_MM`, or leave a copy or a link at the root of the
working tree. mmverify.py belongs to metamath too; say where it is with
`MMVERIFY`, or leave a copy or a link at the root. A gate that skipped any of
them would be saying green about a thing it had not looked at.

Usage:  parley/gate.py
Exits non-zero when anything is not green.
"""
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# How many stages run at once. Four of them hold their own copy of set.mm.
WORKERS = min(4, os.cpu_count() or 1)


def stage(name):
    return [sys.executable, str(ROOT / 'parley' / f'{name}.py')]


# What is run, in the order the report is printed in.
STAGES = [
    ('ruff', None),
    ('declines nobody asked about', stage('declines')),
    ('planted declines', stage('test_declines')),
    ('checker', stage('check')),
    ('planted defects', stage('test_check')),
    ('planted defects the elaborator must report', stage('test_elaborate')),
    ('set.mm labels', stage('labels')),
    ('every library item is cited or tested', stage('tested')),
    ('proofs survive being compressed', stage('test_compress')),
    ('nothing is taken as stated unrecorded', stage('assumed')),
    ('the proofs verify', stage('verify')),
]


def run(argv):
    """One stage, with what it said kept rather than printed."""
    done = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    return done.returncode == 0, done.stdout + done.stderr


def main():
    ruff = shutil.which('ruff')
    wanted = [(what, [ruff, 'check', '.'] if argv is None else argv)
              for what, argv in STAGES]
    if ruff is None:
        wanted = wanted[1:]

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        got = list(pool.map(lambda one: run(one[1]), wanted))

    failed = [] if ruff is not None else ['ruff']
    if ruff is None:
        print('\n=== ruff\nnot on PATH; install it with `pip install ruff`')
    for (what, _argv), (green, said) in zip(wanted, got, strict=True):
        print(f'\n=== {what}')
        print(said, end='')
        if not green:
            failed.append(what)

    print()
    if failed:
        print(f'NOT GREEN: {", ".join(failed)}')
        return 1
    print('green')
    return 0


if __name__ == '__main__':
    sys.exit(main())
