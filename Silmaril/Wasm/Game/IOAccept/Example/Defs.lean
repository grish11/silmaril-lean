module

public import Silmaril.Wasm.Game.IOAccept.Defs
public import Silmaril.Wasm.Game.Examples.Defs

/-! # Traced I/O acceptance of a concrete module: definitions

The data of the worked example of `Silmaril.Wasm.Game.IOAccept.Examples` on `exStart`
(`Silmaril.Wasm.Game.Examples`): an environment answering `values []`, the roles observing
export addresses and import names, and the expected tag list.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.IOAccept.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
  Silmaril.Accept.IO

/-- An environment answering a call with `values []` in the same store, when every host
function with the call's host code has no results (and not otherwise). -/
def unitEnv : SEnv UImp where
  S := Unit
  Ans _ e a _ := a = ⟨e.store, .values []⟩ ∧ ∀ fi ∈ e.store.funcs, fi.code = .host e.target →
    ∀ ps rs, Expand fi.type (.func ps rs) → rs.toList = []
  Div _ _ := False

/-- The roles: an invocation is observed as its export address, a callout as its import. -/
def runRoles : Roles Nat Unit (String × String) Unit where
  entry a _ := some a
  callOut o := some o.imp

/-- The tags of the traced session: the start function's call, the invocation of `"run"`, and
its call. -/
def runTags : List (Tag Nat Unit (String × String) Unit) :=
  [.out ("env", "f"), .enter (some 1), .out ("env", "f")]

end Silmaril.Wasm.Game.IOAccept.Example
