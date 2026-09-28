#!/usr/bin/env bash
# Everything that must pass before a commit, with what can run at once run
# at once.
#
# Two lanes run side by side, because cargo locks each build directory and
# the two lanes build into different ones:
#
#   debug:    cargo clippy, then cargo test          (target/debug)
#   release:  cargo build --release, then parley build, then parley gate
#                                                    (target/release)
#
# Formatting is checked first; it takes a moment and needs no build. Each
# lane's output is kept in a log and printed once both are done, lane by
# lane, so the report reads in order however the two interleaved.
#
# The tests read the built files, and parley build rewrites any that are out
# of date. If it changes one, the tests may have read the old one, so that is
# reported as a failure: rebuilt artifacts are to be committed, and the
# script run again.
#
# Usage:  scripts/precommit.sh     (from anywhere in the working tree)
# Exits non-zero when anything fails.

set -u
cd "$(git rev-parse --show-toplevel)" || exit 2

logs=$(mktemp -d)
trap 'rm -rf "$logs"' EXIT

echo "=== cargo fmt --check"
if ! cargo fmt --check; then
    echo "NOT READY: formatting (run cargo fmt)"
    exit 1
fi

debug_lane() {
    echo "=== cargo clippy --all-targets -- -D warnings"
    cargo clippy --all-targets -- -D warnings || return 1
    echo "=== cargo test"
    cargo test || return 1
}

release_lane() {
    echo "=== cargo build --release"
    cargo build --release || return 1
    echo "=== parley build"
    ./target/release/parley build | tee "$logs/build.out" || return 1
    echo "=== parley gate"
    ./target/release/parley gate || return 1
}

debug_lane >"$logs/debug.log" 2>&1 &
debug=$!
release_lane >"$logs/release.log" 2>&1 &
release=$!

failed=""
wait "$debug" || failed="$failed debug-lane"
wait "$release" || failed="$failed release-lane"

cat "$logs/debug.log"
cat "$logs/release.log"

# A build that changed files ran while the tests were reading them.
if [ -f "$logs/build.out" ] && ! grep -q " 0 changed$" "$logs/build.out"; then
    failed="$failed artifacts-changed"
    echo
    echo "parley build rewrote artifacts: commit them and run this again"
fi

echo
if [ -n "$failed" ]; then
    echo "NOT READY:$failed"
    exit 1
fi
echo "ready to commit"
