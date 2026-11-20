-- Compatibility exception: this executable-only leaf imports the pinned legacy
-- LeanChecker, which cannot be imported from a `module` file. No library imports
-- this driver. See docs/projects/compiler-explorer.md, "Kernel replay driver".
import LeanChecker

/-!
An execution driver for the pinned toolchain's kernel replay, not a new checker.
`LeanChecker.lean` at 67dafde474fbaf278d6d7f822068549bf6e532fa uses the public
`replayFromImports` below: it re-adds the target's declarations through the kernel
on top of its imports. As in the stock CLI, imported declarations are not replayed.

Discover the stock CLI's exact target/descendant set once, rather than scanning
all installed oleans once per target. Replay each selected module in a separate
process (replay.sh); the pinned multi-target CLI crashed in CI.
-/

open Lean

namespace Silmaril.Tools.CompilerExplorer

unsafe def runReplay : IO Unit := do
  initSearchPath (← findSysroot)
  if let some m ← IO.getEnv "SILMARIL_REPLAY_MODULE" then
    if m.isEmpty then throw <| IO.userError "empty replay module"
    replayFromImports m.toName
    IO.println s!"leanchecker {m}: ok"
  else
    let some text ← IO.getEnv "SILMARIL_REPLAY_TARGETS"
      | throw <| IO.userError "missing replay targets"
    let targets := text.splitOn " " |>.filter (! ·.isEmpty)
    if targets.isEmpty then throw <| IO.userError "empty replay targets"
    let sp ← searchPathRef.get
    let paths ← SearchPath.findAllWithExt sp "olean"
    let mut available : List Name := []
    for path in paths do
      if let some m ← searchModuleNameOfFileName path sp then
        available := m :: available
    let mut selected : List Name := []
    for target in targets do
      let target := target.toName
      if target.isAnonymous then throw <| IO.userError "anonymous replay target"
      let mut found := false
      for m in available do
        if target.isPrefixOf m then
          selected := selected.insert m
          found := true
      unless found do throw <| IO.userError s!"Could not find any oleans for: {target}"
    for m in selected do IO.println m

end Silmaril.Tools.CompilerExplorer

#eval Silmaril.Tools.CompilerExplorer.runReplay
