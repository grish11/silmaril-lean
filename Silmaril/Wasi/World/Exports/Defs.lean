module

public import Silmaril.Wasi.World.Defs

/-! # Export calls and returns of legal plays

The export events of a named trace (`WEv.isExp`: export calls `call f args` and returns
`ret f args res`) of a legal play **alternate**, and **each return matches its call** (same
function, same arguments). `ExportAlt o t` is that shape, from a state `o` (`none`: no export
call is open; `some (f, args)`: the call `f args` is open).

Only export events are constrained. A component may make import calls (`req`) and the host may
answer them (`imp`) between an export call and its return. Those events are not export events,
so they are filtered out first (`exportEvents`), and the statement is about what remains.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Component (Val)

/-- The export events of a named trace. -/
def exportEvents (t : List WEv) : List WEv := t.filter WEv.isExp

/-- The open export call of a game position. -/
def openCall {I X : Set FnName} : Pos (nsig I) (nsig X) → Option (FnName × List Val)
  | .idle => none
  | .run q => some (q.1.1, q.2)
  | .wait q _ => some (q.1.1, q.2)

/-- **Alternating, matched export events**: from no open call, a call `f args` opens one; the
open call `f args` is closed by a return `ret f args res` with the same function and
arguments. A last call may stay open. -/
inductive ExportAlt : Option (FnName × List Val) → List WEv → Prop
  /-- The end of the list (an open call may remain). -/
  | nil (o : Option (FnName × List Val)) : ExportAlt o []
  /-- An export call opens. -/
  | call (f : FnName) (a : List Val) {rest : List WEv} :
      ExportAlt (some (f, a)) rest → ExportAlt none (.call f a :: rest)
  /-- The open call returns, with the same function and arguments. -/
  | ret (f : FnName) (a : List Val) (r : Option (List Val)) {rest : List WEv} :
      ExportAlt none rest → ExportAlt (some (f, a)) (.ret f a r :: rest)

end Silmaril.Wasi
