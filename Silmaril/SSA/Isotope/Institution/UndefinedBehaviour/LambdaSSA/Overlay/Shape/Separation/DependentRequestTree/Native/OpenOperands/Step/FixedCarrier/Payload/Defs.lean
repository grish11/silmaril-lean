module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs

/-! # Guarded native control with payload-preserving ordered exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Category.FiniteIteration
open CFG.Dependent (Packet internal_type external_type exitLabel)
open CFG.Dependent.Native (jump packedRequestTo sameRegion exitContinuation)
open ScheduleSearch (StateInventory)
open TwoRequest (Tag)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {A : Syntax.Ty} {states results : Nat}

abbrev Exits (A : Syntax.Ty) := List.replicate 2 A

theorem exit_type (i : Tag) : (Exits A).get i = A := List.getElem_replicate i.isLt

/-- The control and typed request routing are shared with the guarded table.
At a terminal block, a constructor expression reads the incoming packet
and caller and emits a payload at the written ordered exit. -/
structure Endpoint (S : RequestSignature Φ) (R : List Syntax.Ty) (A : Syntax.Ty) where
  control : OpenOperands.Table S R
  output : (i : Fin R.length) → Syntax.Expr [R.get i, R.get control.entry] A

def Endpoint.unit (g : OpenOperands.Table S R) : Endpoint S R .unit :=
  ⟨g, fun _ => .unit⟩

def Endpoint.returnPacket (g : Endpoint S R A) (caller : Syntax.Payload (R.get g.control.entry))
    (p : Packet R) (i : Tag) : Packet (Exits A) :=
  ⟨i, cast (congrArg Syntax.Payload (exit_type i).symm)
    ((g.output p.1).eval ((g.control.bindings caller).push p.2))⟩

def Endpoint.entryRegion (g : Endpoint S R A) : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (R ++ Exits A) :=
  jump (Feedback.internal R (Exits A) g.control.entry) (internal_type g.control.entry) (.var 0)

def Endpoint.blocks (g : Endpoint S R A) (i : Fin R.length) :
    CFG.Dependent.Native.Typed Φ [R.get i, R.get g.control.entry] (R ++ Exits A) :=
  match g.control.row i with
  | .exit j => jump (exitLabel R (Exits A) j) ((external_type (R := R) (L := Exits A) j).trans (exit_type j)) (g.output i)
  | .diverge => CFG.Dependent.Native.diverge
  | .request f arg next typed => packedRequestTo f arg (S.target f)
      (fun j => Feedback.internal R (Exits A) (next j))
      (fun j => (internal_type (L := Exits A) (next j)).trans (typed j))

def Endpoint.native (g : Endpoint S R A) : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A) :=
  ⟨nativeFeedback g.entryRegion g.blocks, nativeFeedback_hasType g.entryRegion g.blocks⟩

def Endpoint.checkNative [DecidableEq Φ] (g : Endpoint S R A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)) : Bool :=
  sameRegion raw.val g.native.val

/-- The code indexes the whole typed exit packet, including the outward tag. -/
def resultBehaviour (codec : Fin results ≃ Packet (Exits A)) :
    Result results states → Behaviour (Exits A).length Unit (Fin states)
  | .ret i t => WithTop.some {Outcome.ret (codec i).1 (codec i).2.val t}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

def Endpoint.rows (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (code : Fin (configs.invocations stores).length) :
    Category.FiniteIteration.Row (configs.invocations stores).length results states :=
  let (p, s) := (configs.invocations stores).get code
  match (g.control.head caller p).execute prim s with
  | .exit i _ t => .stop (.ret (codec.symm (g.returnPacket caller p i)) t)
  | .repeat next t => .repeat (FixedCarrier.encode configs stores (next, t))
  | .fault t => .stop (.fault t)
  | .diverge => .stop .diverge

def Endpoint.markExit (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A)) :
    Result results states → Result results states
  | .ret i t => if g.control.selected (codec i).1 then .ub else .ret i t
  | other => other

def Endpoint.runFinite (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    Result results states :=
  g.markExit codec (execute (g.rows codec caller prim configs stores) (FixedCarrier.encode configs stores (p, s)))

def Endpoint.route {σ : Type v} (g : Endpoint S R A) (caller : Syntax.Payload (R.get g.control.entry))
    (p : Packet R) : StateTransition R σ → Behaviour (R ++ Exits A).length Unit σ
  | .exit i _ t => WithTop.some {Feedback.external R (Exits A) (.ret i (g.returnPacket caller p i).2.val t)}
  | .repeat next t => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) next.1) next.2.val t}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}

/-- The deterministic local transfer keeps the typed incoming packet on a
branch and the complete ordered result on a return. -/
def Endpoint.transition {σ : Type v} (g : Endpoint S R A)
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (p : Packet R × σ) : (Packet R × σ) ⊕ Outcome (Exits A).length Unit σ :=
  match (g.control.head caller p.1).execute prim p.2 with
  | .exit i _ t => .inr (.ret i (g.returnPacket caller p.1 i).2.val t)
  | .repeat next t => .inl (next, t)
  | .fault t => .inr (.fault t)
  | .diverge => .inr .diverge

noncomputable def Endpoint.feedback {σ : Type v} (g : Endpoint S R A)
    (caller : Syntax.Payload (R.get g.control.entry))
    (prim : Syntax.StatePrimitives Φ σ) : Feedback.Run R (Exits A) Unit σ :=
  feedbackRun (.native g.entryRegion) (fun i => .native (g.blocks i)) (Syntax.model prim (g.control.bindings caller)).raw

/-- Close the installed typed rows and apply the ordered exit selection on the
original returned packet at its final machine state. -/
noncomputable def Endpoint.observeAt {σ : Type v} (g : Endpoint S R A)
    (caller : Syntax.Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (p : Packet R) (s : σ) : Behaviour (Exits A).length Unit σ :=
  let M := (Syntax.model prim (g.control.bindings caller)).raw
  (Feedback.close (g.feedback caller prim) (blockPoint p s)).bind fun i a t =>
    LambdaSSA.UB.Overlay.denote
      (exitContinuation (Γ := [R.get g.control.entry]) (L := Exits A) g.control.selected i) (extendModel M a) t

def Endpoint.checkAllInterpreters [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (codec : Fin results ≃ Packet (Exits A)) (caller : Syntax.Payload (R.get g.control.entry))
    (caller' : Syntax.Payload (T.get h.control.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory states) : Bool :=
  let keys := (g.control.queries caller left stores ++ h.control.queries caller' right stores).dedup
  InterpreterScript.checkAll replies stores keys fun prim s =>
    decide ((g.runFinite codec caller prim left stores ⟨g.control.entry, caller⟩ s).refines
      (h.runFinite codec caller' prim right stores ⟨h.control.entry, caller'⟩ s))

/-- Retain exact readback as a separate admission gate for both typed endpoints. -/
def Endpoint.checkAllInterpreters? [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A))
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A))
    (codec : Fin results ≃ Packet (Exits A)) (caller : Syntax.Payload (R.get g.control.entry))
    (caller' : Syntax.Payload (T.get h.control.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory states) :
    Option Bool :=
  if g.checkNative raw && h.checkNative raw' then
    some (g.checkAllInterpreters h codec caller caller' replies left right stores)
  else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
