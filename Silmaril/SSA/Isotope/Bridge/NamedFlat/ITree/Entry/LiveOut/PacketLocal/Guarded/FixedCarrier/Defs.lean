module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs

/-! # Deterministic observations of the named constructor-bit runner -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open Silmaril.Elgot.ITree (Tree vis out diverge)
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet unpack)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (exitContinuation)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table)
open Recognize (Bit Packets)

attribute [local instance] Recognize.requestTypes

abbrev Runtime := ULift.{1} Unit

/-- Expose the complete typed query key before an interpreter is chosen. -/
inductive Request (Φ : Type) : Type → Type
  | call (op : Φ) (argument : Syntax.Payload Bit) : Request Φ (Packet Packets)

def query {Φ : Type} : Query (Recognize.signature Φ) (Request Φ) :=
  fun op arg => vis (.call op arg) (fun reply => pure ⟨reply⟩)

def raw {Φ : Type} : Primitive (Request Φ) Φ Runtime :=
  fun op value =>
    match value with
    | .inl .unit => vis (.call op ⟨.inl .unit, .inl .unit⟩) (pure ∘ Recognize.replyValue ULift.up)
    | .inr .unit => vis (.call op ⟨.inr .unit, .inr .unit⟩) (pure ∘ Recognize.replyValue ULift.up)
    | _ => diverge

abbrev RunTree (Φ : Type) := Tree (Request Φ) (Transfer Runtime)

abbrev Loop : List Syntax.Ty := [.unit]

/-- The two results have the same argument type. Their packed tags still
distinguish their original ordered exit positions. -/
def exitTag : Transfer Runtime → Option (Fin 2)
  | (0, .inl (.pair .unit .unit)) => some 0
  | (0, .inr (.inl (.pair .unit .unit))) => some 1
  | _ => none

/-- Parse a packed weak-tree return into its original ordered tag and payload. -/
abbrev ExitDecoder := Transfer Runtime → Option (Tag × Value Unit)

def unitDecoder : ExitDecoder := fun p => (exitTag p).map fun i => (i, .unit)

def terminal {Φ : Type} {states : Nat} (result : Result 2 states)
    (payload : Value (RunTree Φ) := .unit) :
    Behaviour (Loop ++ Exits).length (RunTree Φ) (Fin states) :=
  match result with
  | .ret i t => WithTop.some {Feedback.external Loop Exits (.ret i payload t)}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

/-- Each successful handler reply resumes the actual weak-tree continuation
at the new machine state. A handler fault retains its state. The row
correspondence supplies a valid packed tag at every recognized return. -/
noncomputable def treeStep {Φ : Type} {states : Nat} (prim : Syntax.Primitives Φ states)
    (tree : RunTree Φ) (s : Fin states) (decode : ExitDecoder := unitDecoder) :
    Behaviour (Loop ++ Exits).length (RunTree Φ) (Fin states) := by
  classical
  exact if h : (out tree).Dom then
    match (out tree).get h with
    | .ret value =>
      match decode value with
      | some (i, payload) => terminal (.ret i s) (Recognize.encodeValue (fun _ => diverge) payload)
      | none => terminal .diverge
    | .vis (.call op arg) next =>
      match prim op arg s with
      | .ret reply t =>
        WithTop.some {Outcome.ret (Feedback.internal Loop Exits 0) (.atom (next (unpack reply))) t}
      | .fault t => terminal (.fault t)
      | .diverge => terminal .diverge
  else terminal .diverge

/-- Reuse positional feedback closure with the residual weak tree as the
internal packet. No new finite search is needed. -/
noncomputable def feedback {Φ : Type} {states : Nat} (prim : Syntax.Primitives Φ states)
    (decode : ExitDecoder := unitDecoder) :
    Feedback.Run Loop Exits (RunTree Φ) (Fin states)
  | .block _ (.atom tree) s => treeStep prim tree s decode
  | _ => terminal .diverge

/-- Recover the decoded constructor payload. Machine states on both
ordinary exits and faults stay in the observation. -/
def project {Φ : Type} {states : Nat} :
    Outcome Exits.length (RunTree Φ) (Fin states) → Outcome Exits.length Unit (Fin states)
  | .ret i a s => .ret i (Recognize.encodeValue (fun _ => ()) a) s
  | .fault s => .fault s
  | .diverge => .diverge

noncomputable def observe {Φ : Type} {states : Nat} (prim : Syntax.Primitives Φ states)
    (tree : RunTree Φ) (s : Fin states) (decode : ExitDecoder := unitDecoder) : Behaviour Exits.length Unit (Fin states) :=
  (Feedback.close (feedback prim decode) (.block 0 (.atom tree) s)).map (Set.image project)

/-- Interpret a finite output code with its exact decoded return payload. -/
def resultWithPayload {states : Nat} (payload : Tag → Value Unit) :
    Result 2 states → Behaviour Exits.length Unit (Fin states)
  | .ret i s => WithTop.some {Outcome.ret i (payload i) s}
  | .fault s => WithTop.some {Outcome.fault s}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

/-- The annotation belongs to the outward continuation. Entry, rows, and
the emitted native CFG are the same as in exact lexical recognition. -/
abbrev withSelectedExits {Φ : Type} (op : Φ) (routes : Recognize.Routes)
    (selected : Tag → Bool) : Table (Recognize.signature Φ) Packets :=
  { Recognize.guardedTable op routes with selected := selected }

/-- Apply the native exit continuations to the named result at its decoded
ordered tag and final machine state. -/
noncomputable def decorate {Φ : Type} {states : Nat} (prim : Syntax.Primitives Φ states)
    (selected : Tag → Bool) (observed : Behaviour Exits.length Unit (Fin states))
    (exitType : Syntax.Ty := .unit) :
    Behaviour Exits.length Unit (Fin states) :=
  let M := (Syntax.model prim Syntax.emptyBindings).raw
  observed.bind fun i a t => LambdaSSA.UB.Overlay.denote (exitContinuation (Γ := []) (L := List.replicate 2 exitType) selected i) (extendModel M a) t

/-- Observe the original mutable runner with its ordered unit exits and empty
live-outs under a deterministic typed primitive interpreter. The optional
selection uses those same ordered exit positions. -/
noncomputable def observeNamed {Φ : Type} {states : Nat} {V K : Type 1}
    [DecidableEq V] [DecidableEq K] (source : CFG V K Φ) (names : Fin 5 ≃ K)
    (input : V → Value Runtime) (prim : Syntax.Primitives Φ states) (s : Fin states)
    (selected : Tag → Bool := fun _ => false) : Behaviour Exits.length Unit (Fin states) :=
  decorate prim selected (observe prim (LiveOut.observeRaw raw [names 3, names 4] (fun _ => []) source input) s)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
