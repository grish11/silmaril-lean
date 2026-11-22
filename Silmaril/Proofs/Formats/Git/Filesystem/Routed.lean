module

public import Silmaril.Formats.Git.Filesystem.Routed.Defs

public section

namespace Silmaril.Proofs.Formats.Git.Filesystem

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey)

theorem locateWith_agree {left right : ChildLookup}
    (agree : ∀ ⦃root key first second⦄, left root key = .ok first → right root key = .ok second → first = second)
    {root : Cid} {path : List ByteKey} {first second : Option (Entry Cid)}
    (firstOk : locateWith left root path = .ok first) (secondOk : locateWith right root path = .ok second) :
    first = second := by
  induction path generalizing root with
  | nil => simp [locateWith] at firstOk secondOk; exact firstOk.symm.trans secondOk
  | cons key rest ih =>
    cases leftHit : left root key with
    | error fault => simp [locateWith, leftHit, Bind.bind, Except.bind] at firstOk
    | ok firstChild =>
      cases rightHit : right root key with
      | error fault => simp [locateWith, rightHit, Bind.bind, Except.bind] at secondOk
      | ok secondChild =>
        have same := agree leftHit rightHit
        subst secondChild
        cases firstChild with
        | none =>
          cases rest <;> simp [locateWith, leftHit, rightHit, Bind.bind, Except.bind] at firstOk secondOk <;>
            exact firstOk.symm.trans secondOk
        | some entry =>
          cases rest with
          | nil => simp [locateWith, leftHit, rightHit, Bind.bind, Except.bind] at firstOk secondOk
                   exact firstOk.symm.trans secondOk
          | cons next tail =>
            by_cases tree : entry.mode = .directory
            · apply ih (root := entry.target)
              · simpa [locateWith, leftHit, Bind.bind, Except.bind, tree] using firstOk
              · simpa [locateWith, rightHit, Bind.bind, Except.bind, tree] using secondOk
            · simp [locateWith, leftHit, tree, Bind.bind, Except.bind] at firstOk

end Silmaril.Proofs.Formats.Git.Filesystem
