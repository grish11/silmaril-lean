#!/usr/bin/env bash
# The ELF pages are derived from the checked theorems, and nothing else (tools/elf-pages): one
# generation into a temporary directory, verified, then edits that move a byte range, re-associate
# a theorem or a function row, widen a coverage class, hide axioms or link a contract to another
# function, each of which --verify must reject (`elf-pages --self-test`).
set -euo pipefail
cd "$(dirname "$0")/../.."
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
lake env .lake/build/bin/elf-pages --self-test "$out"
