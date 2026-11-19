#!/usr/bin/env bash
# Replay the kernel on the compiler explorer's evidence modules with the toolchain's `leanchecker`
# (`make compiler-explorer-check` runs it). Each named module's own declarations are re-added to an
# environment, through the kernel, on top of its imports as loaded from their .olean files; the
# imports are not replayed (`--fresh`, the whole closure with Mathlib, is not run). It is the same
# kernel as `lake build`, run again on the stored declarations, not an independent implementation.
set -euo pipefail
cd "$(dirname "$0")/../.."
LAKE="${LAKE:-lake}"
modules=(
  CompilesToExamples.Explorer.C2C.Runs
  CompilesToExamples.Explorer.C2C.Elaborates
  CompilesToExamples.Straight.Proofs.Elaborates
  CompilesToExamples.Branch.Proofs.Elaborates
  Silmaril.Proofs.Compiler.CompilesTo.Sim.Compose
  Silmaril.Proofs.Compiler.Explorer.Basic
  Silmaril.Proofs.Compiler.Explorer.Det
  Silmaril.Compiler.Explorer.Decompiled.Thms
  Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer
  CompilesToExamples.Explorer.Builds
  CompilesToExamples.Explorer.Code
  CompilesToExamples.Explorer.Decompiled
  CompilesToExamples.Explorer.Rows
  Silmaril.Proofs.Project.Shapes.CompilesTo.Translate
  Silmaril.Project.Shapes.C.Additive.Thms
  Silmaril.Proofs.Compiler.Explorer.Text
  Silmaril.Compiler.Explorer.Text.Thms
  CompilesToExamples.Explorer.TypeError
  Silmaril.Proofs.Compiler.C.Compact
  Silmaril.Proofs.Compiler.C.CompactBody
  Silmaril.Compiler.C.Compact.Thms
  CompilesToExamples.Explorer.Compact.Checks
  CompilesToExamples.Explorer.Compact.Core
)
jobs=$(nproc)
if (( jobs > 6 )); then jobs=6; fi
start=$(date +%s)
printf '%s\n' "${modules[@]}" |
  LEAN_NUM_THREADS=1 timeout 1200 "$LAKE" env xargs -r -n 1 -P "$jobs" bash -c '
    printf "leanchecker: %s\n" "$1"
    exec leanchecker "$1"
  ' replay
echo "leanchecker: ${#modules[@]} modules ok ($(( $(date +%s) - start )) s)"
