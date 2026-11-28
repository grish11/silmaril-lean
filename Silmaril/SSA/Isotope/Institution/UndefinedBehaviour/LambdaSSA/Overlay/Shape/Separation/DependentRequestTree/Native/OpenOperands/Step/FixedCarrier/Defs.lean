module

public import Mathlib.Data.List.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Defs

/-! # Exhaustive interpreter restrictions for finite guarded CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open ScheduleSearch (StateInventory)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {states : Nat}

namespace InterpreterScript

/-- The entire answer alphabet at a key, including final stores for
successes and faults, and one ordinary divergence. -/
def choices (replies : ReplyEnumeration S) (stores : StateInventory states) (q : Query Φ states) :
    List (Syntax.Reply (instrTrg q.op) states) :=
  .diverge :: (stores.values.map Syntax.Reply.fault) ++
    (replies.packets q.op).flatMap fun p => stores.values.map fun t => (Row.success q p t).2

/-- Enumerate all assignments on the given keys. The checker supplies a
deduplicated union of the two programs' query supports. -/
def assignments (replies : ReplyEnumeration S) (stores : StateInventory states) :
    List (Query Φ states) → List (List (Row Φ states))
  | [] => [[]]
  | q :: rest =>
    let tails := assignments replies stores rest
    (choices replies stores q).flatMap fun answer => tails.map fun tail => ⟨q, answer⟩ :: tail

/-- Unlisted queries use the same total fallback as schedule replay. -/
def interpret [DecidableEq Φ] (script : List (Row Φ states)) : Syntax.Primitives Φ states :=
  extend script (fun _ _ _ => .diverge)

/-- Test the existing interpreter restrictions over their common key support. -/
def checkAll [DecidableEq Φ] (replies : ReplyEnumeration S) (stores : StateInventory states)
    (keys : List (Query Φ states)) (test : Syntax.Primitives Φ states → Fin states → Bool) : Bool :=
  (assignments replies stores keys).all fun script =>
    stores.values.all (test (interpret script))

end InterpreterScript

/-- All typed invocations, including configurations unreachable from the
entry under some or all restrictions. The caller is held fixed separately. -/
def ConfigurationEnumeration.invocations (configs : ConfigurationEnumeration R) (stores : StateInventory states) :
    List (Packet R × Fin states) :=
  configs.configs.product stores.values

theorem ConfigurationEnumeration.invocation_mem (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R × Fin states) : p ∈ configs.invocations stores :=
  List.mem_product.mpr ⟨configs.complete p.1, stores.complete p.2⟩

/-- Use the full typed key at a request head and no key at an exit. -/
def Head.query? (head : Head S R) (s : Fin states) : Option (InterpreterScript.Query Φ states) :=
  match head with
  | .exit .. | .diverge => none
  | .request f arg _ => some ⟨f, arg, s⟩

def Table.queries (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) : List (InterpreterScript.Query Φ states) :=
  (configs.invocations stores).filterMap fun (p, s) => (g.head caller p).query? s

namespace FixedCarrier

def encode (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R × Fin states) : Fin (configs.invocations stores).length :=
  ⟨(configs.invocations stores).idxOf p, List.idxOf_lt_length_of_mem (configs.invocation_mem stores p)⟩

/-- A bounded classifier runs the native rows before applying the designated
UB continuation. The bound is the length of the invocation inventory,
even when that inventory repeats entries. -/
def rows (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (code : Fin (configs.invocations stores).length) :
    Category.FiniteIteration.Row (configs.invocations stores).length 2 states :=
  let input := (configs.invocations stores).get code
  match (g.head caller input.1).execute prim input.2 with
  | .exit i _ t => .stop (.ret i t)
  | .repeat next t => .repeat (encode configs stores (next, t))
  | .fault t => .stop (.fault t)
  | .diverge => .stop .diverge

end FixedCarrier

def Table.runFinite (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    Result 2 states :=
  g.markExit
    (execute (FixedCarrier.rows g caller prim configs stores) (FixedCarrier.encode configs stores (p, s)))

variable [DecidableEq Φ]

/-- Compare the existing finite results under each interpreter restriction.
The comparison can retain extra information determined by each terminal result. -/
def Table.checkAllInterpretersBy (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) (compare : Result 2 states → Result 2 states → Bool) : Bool :=
  let keys := (g.queries caller left stores ++ h.queries caller' right stores).dedup
  InterpreterScript.checkAll replies stores keys fun prim s =>
    compare (g.runFinite caller prim left stores ⟨g.entry, caller⟩ s)
      (h.runFinite caller' prim right stores ⟨h.entry, caller'⟩ s)

def Table.checkAllInterpreters (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) : Bool :=
  g.checkAllInterpretersBy h caller caller' replies left right stores (fun result other => decide (result.refines other))

/-- Exact readback is a separate admission gate for each original typed CFG. -/
def Table.checkAllInterpreters? (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory states) : Option Bool :=
  if g.checkNative raw && h.checkNative raw' then
    some (g.checkAllInterpreters h caller caller' replies left right stores)
  else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
