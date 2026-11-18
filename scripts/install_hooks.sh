#!/usr/bin/env bash
# Use the repository's git hooks (.githooks/) in this clone. Git does not take hooks from a clone by itself, so run
# this once after cloning:
#
#     scripts/install_hooks.sh
#
# .githooks/pre-commit then runs the fast dead-code check (scripts/dead_code_fast.py) on every commit that changes
# a Lean file or a note of formalisations/, and .githooks/pre-merge-commit on a merge that git commits by itself.
# `git config --unset core.hooksPath` undoes it. scripts/build.sh reminds a clone that has no hooks of this script.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
git config core.hooksPath .githooks
echo "core.hooksPath = .githooks: scripts/dead_code_fast.py runs before a commit or a merge that changes a Lean file"
