module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Engine

/-- The ordered flat traversal. In `Prog` it runs the canonical children; in
`ExceptT` over `Prog` a typed refusal stops the traversal without undoing the
prefix. Canonical traps remain operations of the underlying program. -/
def flatSequence {m : Type → Type} [Monad m] (lower : Nat → Field → m (List FlatValue)) :
    List Field → Nat → m (List FlatValue)
  | [], _ => pure []
  | field :: rest, index => do
    let words ← lower index field
    let tailWords ← flatSequence lower rest (index + 1)
    return words ++ tailWords

/-- The record/tuple cursor advances only after the child succeeds, using the
same width for aligning that field and advancing past it. The canonical traversal
reads the width here; the compiled traversal supplies its previously read width. -/
def memorySequence {m : Type → Type} [Monad m] (readWidth : m AddrType)
    (store : Nat → Field → Nat → m Unit) : List Field → Nat → Nat → m Unit
  | [], _, _ => pure ()
  | field :: rest, cursor, index => do
    let width ← readWidth
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    store index field ptr
    memorySequence readWidth store rest (ptr + area.size) (index + 1)

/-- In-place element writes, with the stride fixed by the enclosing collection. -/
def elementSequence {m : Type → Type} [Monad m] (store : Nat → Field → Nat → m Unit) :
    List Field → Nat → Nat → Nat → m Unit
  | [], _, _, _ => pure ()
  | field :: rest, stride, ptr, index => do
    store index field ptr
    elementSequence store rest stride (ptr + stride) (index + 1)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
