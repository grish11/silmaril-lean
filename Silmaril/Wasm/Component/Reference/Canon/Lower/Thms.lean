module

public import Silmaril.Wasm.Component.Reference.Canon.Lower.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
import Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift

/-!
# `Canon.Lower`: laws of the component reference

Theorems of the component reference copy `Canon.Lower`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Lower`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

/-- Store operations of the executable memory lift for a closed WIT type. -/
theorem loadAt_scoped (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (type : WIT.ClosedType RtId) (ptr : Nat) :
    Prog.Every (LowerSt.ValueLiftOp cx) (loadAt lim q cx width type ptr : P E σ Val) :=
  Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift.loadAt_scoped lim q cx width type ptr

/-- Store operations of the executable flat lift for a closed WIT type. -/
theorem liftFlatAt_scoped (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (type : WIT.ClosedType RtId) (cursor : FlatCursor) :
    Prog.Every (LowerSt.ValueLiftOp cx) (liftFlatAt lim q cx width type cursor : P E σ _) :=
  Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift.liftFlatAt_scoped lim q cx width type cursor

/-- Classification of the executable typed value lift, in either the flat or
spilled-memory route, at its actual instance and borrow scope. -/
theorem liftFlatValues_scoped (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (max : Nat) (vi : FlatCursor) (ts : List (WIT.ClosedType RtId)) :
    Prog.Every (LowerSt.ValueLiftOp cx) (liftFlatValues lim q cx max vi ts : P E σ _) :=
  Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift.liftFlatValues_scoped lim q cx max vi ts

/-- The direct and spilled argument lifts, including recursive loads and
handle transfers, issue only store reads, store modifications and traps. -/
theorem lowerOnStart_every (lim : Limits) (q : Quirks) (caller : CallerId)
    {allow : Op E σ → Prop} (get : allow .get) (modify : ∀ update, allow (.modify update))
    (fail : ∀ reason, allow (.trap reason)) :
    Prog.Every (S := Eff E σ) allow (lowerOnStart lim q caller) :=
  Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift.lowerOnStart_every
    lim q caller get modify fail

/-- All recursively reached modifications in direct and spilled argument
lifting preserve the caller shapes, while their positions and other store data may change. -/
theorem lowerOnStart_caller_shape (lim : Limits) (q : Quirks) (caller : CallerId) :
    Prog.Every LowerSt.argumentLiftOp (lowerOnStart lim q caller : P E σ (List Val)) :=
  Silmaril.Proofs.Wasm.Component.Reference.Canon.Lower.StoreLift.lowerOnStart_caller_shape lim q caller

namespace P.Inv

variable {I : CStore E → Prop} {W : σ → Prop}

theorem handlesAddSubtask {inst : InstId} {sub : SubtaskId}
    (h : ∀ i s, I s → I (LowerSt.addSubtaskSt inst sub i s)) :
    P.InvW I W (Canon.handlesAddSubtask inst sub : P E σ Nat) :=
  bind (getInst inst) fun st => by
    cases st.addHandle? (.waitable (.subtask sub)) with
    | none => exact trap _
    | some r => exact bind (modifyStore (h _)) fun _ => pure _

theorem maybeOnProgress (h : LowerPres I) (s : SubtaskId) :
    P.InvW I W (Canon.maybeOnProgress s : P E σ Unit) :=
  bind (getObj _ _) fun _ =>
    ite (Waitable.setPendingEvent_inv (h.setPending _ _)) (pure _)

theorem lowerOnStart (h : LowerPres I) (lim : Limits) (q : Quirks) (c : CallerId) :
    P.InvW I W (Canon.lowerOnStart lim q c : P E σ (List Val)) := by
  unfold Canon.lowerOnStart
  refine bind (getObj _ _) fun x => ?_
  cases x with
  | lower s cx flatArgs pos ft maxParams _ =>
    exact bind (maybeOnProgress h s) fun _ => bind (modifyStore (h.start s)) fun _ =>
      bind (liftFlatValues h.load _ _ _ _ _ _) fun _ =>
        bind (modifyStore (h.setCallerPos _ _)) fun _ => pure _
  | host => exact internal _
  | sub => exact internal _

theorem canonLower (h : LowerPres I) (lim : Limits) (q : Quirks) (callee : FuncId)
    (ft : WIT.FuncType Empty RtId) (opts : CanonOpts E) (inst : InstId)
    (flatArgs : List FlatValue) :
    P.InvW I W (Canon.canonLower lim q callee ft opts inst flatArgs : P E σ (List FlatValue)) := by
  unfold Canon.canonLower Canon.lowerAfterCallee Canon.lowerAfterCancel
  refine bind (getInst _) fun _ => bind (trapIf _ _) fun _ => ?_
  refine bind (allocObj _ _ (h.allocSubtask _)) fun s => ?_
  refine bind (allocObj _ _ (h.allocCaller _)) fun c => ?_
  refine bind (callCancel _) fun oc => bind (modifyStore (h.setOnCancel _ _)) fun _ => ?_
  refine ite ?_ ?_
  · refine bind (gets _) fun _ => bind (ite ?_ (pure _)) fun _ =>
      bind (Subtask.deliverResolve_inv (h.deliver s)) fun _ =>
        bind (getObj _ _) fun _ => pure _
    exact Thread.waitUntil_inv _ _ _ fun t s' => h.startWaiting t _ s'
  · refine bind (gets _) fun _ => ite ?_ ?_
    · exact bind (Subtask.deliverResolve_inv (h.deliver s)) fun _ => pure _
    · exact bind (handlesAddSubtask (h.addSubtask _ _)) fun _ => bind (getObj _ _) fun _ => pure _

end P.Inv

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop} {W : σ → Prop}

theorem lowerOnResolve (h : LowerPres I) (lim : Limits) (q : Quirks) (c : CallerId)
    (r : Option (List Val)) :
    P.InvW I W (Canon.lowerOnResolve lim q c r : P E σ Unit) := by
  unfold Canon.lowerOnResolve
  refine bind (getObj _ _) fun x => ?_
  cases x with
  | lower s cx flatArgs pos ft _ maxResults =>
    refine bind (maybeOnProgress h s) fun _ => ?_
    cases r with
    | none =>
      exact bind (ite (modifyStore (h.releaseLends s)) (pure _)) fun _ =>
        bind (getObj _ _) fun _ =>
        ite (Subtask.resolve_inv (h.resolve _ _ _)) (Subtask.resolve_inv (h.resolve _ _ _))
    | some vs =>
      exact bind (lowerFlatValues h.store _ _ _ _ _ _ _) fun _ =>
        bind (ite (modifyStore (h.releaseLends s)) (pure _)) fun _ =>
          Subtask.resolve_inv (h.resolve _ _ _)
  | host => exact internal _
  | sub => exact internal _

end P.Inv

end Silmaril.Wasm.Component.Canon
