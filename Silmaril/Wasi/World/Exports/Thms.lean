module

public import Silmaril.Wasi.World.Exports.Defs
public import Silmaril.Games.Play.Defs

/-! # Export calls and returns of legal plays: theorems

* **`exportAlt_of_legal`**: the export events of the named trace of every legal play of
  `nsig I ↠ nsig X` alternate and match (`ExportAlt none`). The general form,
  `exportAlt_of_path`, starts from any game position, with that position's open call.

The proof reads the legality automaton (`Silmaril.Games.Path`). An Opponent question opens an
export call (`call`), and the Proponent answer to the same question closes it (`ret`, with the
question's function and arguments). Import questions and answers (`req`, `imp`) leave the open
call unchanged, and they are not export events.

`Silmaril.Wasi.IOAccept.ret_after_call` (the next export event after a call is its return) is a
consequence.
-/

@[expose] public section

namespace Silmaril.Wasi

open Silmaril.Games

theorem exportEvents_cons (e : WEv) (t : List WEv) :
    exportEvents (e :: t) = if e.isExp then e :: exportEvents t else exportEvents t := by
  simp only [exportEvents, List.filter_cons]

/-- **The export events of a play read from a position alternate and match.** -/
theorem exportAlt_of_path {I X : Set FnName} {x y : Pos (nsig I) (nsig X)}
    {s : List (Move (nsig I) (nsig X))} (h : Path x s y) :
    ExportAlt (openCall x) (exportEvents (wtrace s)) := by
  induction h with
  | nil => exact .nil _
  | cons hst _ ih =>
    rename_i x y z o s
    cases hst with
    | ask q => exact .call _ _ ih
    | call q m => simpa [wtrace, wev, exportEvents_cons, WEv.isExp, openCall] using ih
    | reply q m n => simpa [wtrace, wev, exportEvents_cons, WEv.isExp, openCall] using ih
    | ret q r => exact .ret _ _ _ ih

/-- **The export events of a legal play alternate and match.** -/
theorem exportAlt_of_legal {I X : Set FnName} {s : List (Move (nsig I) (nsig X))}
    (hs : Legal s) : ExportAlt none (exportEvents (wtrace s)) := by
  obtain ⟨y, hy⟩ := hs
  exact exportAlt_of_path hy

end Silmaril.Wasi
