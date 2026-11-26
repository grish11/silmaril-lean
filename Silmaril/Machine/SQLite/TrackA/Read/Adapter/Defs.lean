module

public import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics.TrackA.Interaction (Signature ITree Coalgebra)
open Read.Interaction (VfsSignature vfsExchanges)

structure Acquire where
  target : PageRead.SlotId
  page : PageRead.Page

structure Acquired where
  result : Except PageRead.FillError Bytes
  cache : PageRead.Cache

abbrev PagerSignature : Signature := ⟨Acquire, fun _ => Acquired⟩
abbrev LeafResult := Read.Result × PageRead.Cache

/-- One VM-to-Pager call and the continuation consuming its typed reply. -/
structure SeekCall where
  request : PagerSignature.Request
  resume : PagerSignature.Response request → LeafResult

def leafCall (request : Acquire) (leaf : File.View → Read.Result) : SeekCall :=
  ⟨request, fun reply =>
    let after := Read.finishAcquire leaf (⟨reply.result, (), reply.cache, []⟩ : PageRead.Outcome Unit)
    (after.result, after.cache)⟩

def stagedCall (request : Acquire) (key : Int64) : SeekCall :=
  leafCall request (fun view => Read.seekLeaf view request.page.number key)

def pagerTree (call : SeekCall) : ITree PagerSignature LeafResult where
  State := Option Acquired
  root := fun _ => none
  unfold
    | none => .vis call.request some
    | some reply => .ret (call.resume reply)

inductive TwoSeeks where
  | first
  | second (firstResult : LeafResult)
  | done (firstResult secondResult : LeafResult)

/-- Both acquisitions are answered by the same handler. -/
def pagerTwice (call : SeekCall) : ITree PagerSignature (LeafResult × LeafResult) where
  State := TwoSeeks
  root := fun _ => .first
  unfold
    | .first => .vis call.request fun reply => .second (call.resume reply)
    | .second first => .vis call.request fun reply => .done first (call.resume reply)
    | .done first second => .ret (first, second)

/-- The cache passed to each Pager call is the cache returned by the last call. -/
abbrev PagerState (Backing : Type) := Backing × PageRead.Cache × Trace

/-- Handler state carries the actual file and completed exchanges. -/
abbrev Recorded (Backing : Type) := Backing × Trace

def handlePager {Backing : Type} (backing : Handler Backing) :
    Coalgebra.Handler PagerSignature (PagerState Backing) :=
  fun (file, cache, trace) request =>
    let (acquired, after, nextCache) :=
      Read.Interaction.pagerHandler backing (file, cache) (request.target, request.page)
    (⟨acquired.result, acquired.cache⟩, after, nextCache, trace ++ acquired.trace)

def handleVfs {Backing : Type} (backing : Handler Backing) :
    Coalgebra.Handler VfsSignature (Recorded Backing) :=
  fun (file, trace) request =>
    let (reply, after) := backing file request
    (reply, after, trace ++ [⟨request, reply⟩])

/-- The handled tree reaches the stated return and handler poststate. -/
def Returns {S : Signature} {State Result : Type} (tree : ITree S Result)
    (handler : Coalgebra.Handler S State) (before after : State) (result : Result) : Prop :=
  let interpreted := tree.unfold.handle (T := VfsSignature) handler
  ∃ final, interpreted.Silent (tree.root (), before) (final, after) ∧
    interpreted (final, after) = .ret result

/-- The open tree can reach a completed return with these request/reply pairs. -/
def Observes {Backing : Type} (tree : ITree VfsSignature LeafResult)
    (outcome : Read.Outcome Backing) : Prop :=
  Silmaril.Semantics.TrackA.Interaction.Trace.finite (vfsExchanges outcome.exchanges)
    (.returned (outcome.result, outcome.cache)) ∈ tree.unfold.observes (tree.root ())

end Silmaril.Machine.SQLite.TrackA.Read.Adapter
