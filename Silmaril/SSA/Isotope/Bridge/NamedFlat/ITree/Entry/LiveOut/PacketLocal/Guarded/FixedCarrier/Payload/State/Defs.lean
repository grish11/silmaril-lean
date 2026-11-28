module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Thms

/-! # Interpreting the actual named weak tree over a deterministic store type -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open Silmaril.Elgot.ITree (out diverge)
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (unpack)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (exitContinuation)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

attribute [local instance] Recognize.requestTypes

universe v

variable {Φ : Type} {σ : Type v}

def terminalOn (o : Outcome Exits.length (RunTree Φ) σ) :
    Behaviour (Loop ++ Exits).length (RunTree Φ) σ :=
  WithTop.some {Feedback.external Loop Exits o}

noncomputable def treeStepOn (prim : Syntax.StatePrimitives Φ σ)
    (tree : RunTree Φ) (s : σ) (decode : ExitDecoder) :
    Behaviour (Loop ++ Exits).length (RunTree Φ) σ := by
  classical
  exact if h : (out tree).Dom then
    match (out tree).get h with
    | .ret value =>
      match decode value with
      | some (i, payload) => terminalOn (.ret i (Recognize.encodeValue (fun _ => diverge) payload) s)
      | none => terminalOn .diverge
    | .vis (.call op arg) next =>
      match prim op arg s with
      | .ret reply t =>
        WithTop.some {Outcome.ret (Feedback.internal Loop Exits 0) (.atom (next (unpack reply))) t}
      | .fault t => terminalOn (.fault t)
      | .diverge => terminalOn .diverge
  else terminalOn .diverge

noncomputable def feedbackOn (prim : Syntax.StatePrimitives Φ σ) (decode : ExitDecoder) :
    Feedback.Run Loop Exits (RunTree Φ) σ
  | .block _ (.atom tree) s => treeStepOn prim tree s decode
  | _ => terminalOn .diverge

def projectOn :
    Outcome Exits.length (RunTree Φ) σ → Outcome Exits.length Unit σ
  | .ret i a s => .ret i (Recognize.encodeValue (fun _ => ()) a) s
  | .fault s => .fault s
  | .diverge => .diverge

noncomputable def observeOn (prim : Syntax.StatePrimitives Φ σ)
    (tree : RunTree Φ) (s : σ) (decode : ExitDecoder) : Behaviour Exits.length Unit σ :=
  (Feedback.close (feedbackOn prim decode) (.block 0 (.atom tree) s)).map (Set.image projectOn)

noncomputable def decorateOn (prim : Syntax.StatePrimitives Φ σ) (selected : Fin Exits.length → Bool)
    (observed : Behaviour Exits.length Unit σ) (exitType : Syntax.Ty) :
    Behaviour Exits.length Unit σ :=
  let M := (Syntax.model prim Syntax.emptyBindings).raw
  observed.bind fun i a t => LambdaSSA.UB.Overlay.denote
    (exitContinuation (Γ := []) (L := List.replicate 2 exitType) selected i) (extendModel M a) t

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
