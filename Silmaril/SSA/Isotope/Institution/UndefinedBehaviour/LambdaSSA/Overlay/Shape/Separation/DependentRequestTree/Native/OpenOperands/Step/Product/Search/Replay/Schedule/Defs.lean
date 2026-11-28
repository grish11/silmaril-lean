module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Defs

/-! # Executable schedules in a fixed finite machine-state carrier -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open InterpreterScript (Query)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {states : Nat}

namespace InterpreterScript

def sameAnswer {A : Syntax.Ty} : Syntax.Reply A states → Syntax.Reply A states → Bool
  | .ret p s, .ret q t => decide (p.val = q.val ∧ s = t)
  | .fault s, .fault t => decide (s = t)
  | .diverge, .diverge => true
  | _, _ => false

/-- Reject a new row as soon as any previously recorded answer at its key
differs, including a different final machine state. -/
def canAppend [DecidableEq Φ] (rows : List (Row Φ states)) (row : Row Φ states) : Bool :=
  rows.all fun previous =>
    match previous.lookup row.1 with
    | none => true
    | some answer => sameAnswer answer row.2

def canAppendAll [DecidableEq Φ] : List (Row Φ states) → List (Row Φ states) → Bool
  | _, [] => true
  | rows, row :: rest => canAppend rows row && canAppendAll (rows ++ [row]) rest

end InterpreterScript

namespace ScheduleSearch

structure StateInventory (states : Nat) where
  values : List (Fin states)
  complete : ∀ state, state ∈ values

/-- The state-independent part of a successful query recorded by the
reported path. Its continuation is already fixed by the path. -/
structure Request (S : RequestSignature Φ) where
  op : Φ
  arg : Syntax.Payload (instrSrc op)
  reply : Packet (S.replies op)

def Request.row (req : Request S) (s t : Fin states) : InterpreterScript.Row Φ states :=
  InterpreterScript.Row.success ⟨req.op, req.arg, s⟩ req.reply t

def Request.ofHead? [DecidableEq Φ] (head : Head S R) (reply : Σ f : Φ, Packet (S.replies f)) :
    Option (Request S) :=
  match head with
  | .exit .. | .diverge => none
  | .request op arg _ =>
    if eq : reply.1 = op then some ⟨op, arg, eq ▸ reply.2⟩ else none

/-- Associate the reported reply with its input at each visited left
configuration. Correctness is stated for a certified shared product path. -/
def requests? [DecidableEq Φ] (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) :
    ProductConfig R T → List (ProductEdge S R T) → Option (List (Request S) × ProductConfig R T)
  | atPair, [] => some ([], atPair)
  | atPair, edge :: rest => do
    let req ← Request.ofHead? (g.head caller atPair.1) edge.1
    let (requests, final) ← requests? g caller edge.2 rest
    return (req :: requests, final)

inductive Schedules : List (Request S) → Fin states → List (Fin states) →
    Fin states → List (InterpreterScript.Row Φ states) → Prop where
  | nil (s : Fin states) : Schedules [] s [] s []
  | cons {req rest s t stores final rows} : Schedules rest t stores final rows →
    Schedules (req :: rest) s (t :: stores) final (req.row s t :: rows)

structure Witness (Φ : Type u) [HasTy Φ Syntax.Ty] (states : Nat) where
  stores : List (Fin states)
  final : Fin states
  rows : List (InterpreterScript.Row Φ states)
  tests : List (InterpreterScript.Row Φ states)

/-- Includes the successful replies and any terminal tests from the search. -/
def Witness.interpreter [DecidableEq Φ] (w : Witness Φ states) : Syntax.Primitives Φ states :=
  InterpreterScript.extend (w.rows ++ w.tests) (fun _ _ _ => .diverge)

/-- Search branches in inventory order. Consistency is checked before
recursing, and the terminal tests share the same accumulated script. -/
def search [DecidableEq Φ] (inventory : StateInventory states)
    (tests : Fin states → List (InterpreterScript.Row Φ states)) :
    List (Request S) → Fin states → List (InterpreterScript.Row Φ states) → Option (Witness Φ states)
  | [], s, rows =>
    if InterpreterScript.canAppendAll rows (tests s) then some ⟨[], s, rows, tests s⟩ else none
  | req :: rest, s, rows =>
    inventory.values.findSome? fun t =>
      let row := req.row s t
      if InterpreterScript.canAppend rows row then
        (search inventory tests rest t (rows ++ [row])).map fun w => { w with stores := t :: w.stores }
      else none

end ScheduleSearch

/-- Schedule a reported path at the supplied initial state. Terminal tests
are produced from the final state and may be empty. -/
def Table.searchSchedule [DecidableEq Φ] (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (start : ProductConfig R T) (path : List (ProductEdge S R T)) (initial : Fin states)
    (inventory : ScheduleSearch.StateInventory states)
    (tests : Fin states → List (InterpreterScript.Row Φ states) := fun _ => []) :
    Option (ScheduleSearch.Witness Φ states) := do
  let (requests, _) ← ScheduleSearch.requests? g caller start path
  ScheduleSearch.search inventory tests requests initial []

/-- Read the two pending query heads for a fault-versus-divergence test.
The schedule search will check its consistency with the successful prefix. -/
def Table.queryTests? (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (point : ProductConfig R T) (faultState : Fin states) :
    Option (Fin states → List (InterpreterScript.Row Φ states)) :=
  match g.head caller point.1, h.head caller' point.2 with
  | .request op arg _, .request op' arg' _ =>
    some fun final => [⟨⟨op, arg, final⟩, .fault faultState⟩, ⟨⟨op', arg', final⟩, .diverge⟩]
  | _, _ => none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
