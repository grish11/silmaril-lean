module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Defs

/-! # One request-guarded step of an exact native CFG table -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet unpack)
open TwoRequest (Exits Tag)

universe u x

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {σ : Type x}

/-- A row leaves at its written position, diverges ordinarily, or performs one request.
Its continuation stores the exact next label and incoming payload. -/
inductive Head (S : RequestSignature Φ) (R : List Syntax.Ty) where
  | exit (tag : Tag) (selected : Bool)
  | diverge
  | request (f : Φ) (arg : Syntax.Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Packet R)

inductive StateTransition (R : List Syntax.Ty) (σ : Type x) where
  | exit (tag : Tag) (selected : Bool) (final : σ)
  | repeat (next : Packet R) (final : σ)
  | fault (final : σ)
  | diverge

abbrev Transition (R : List Syntax.Ty) (states : Nat) := StateTransition R (Fin states)

abbrev Transition.repeat {states : Nat} (p : Packet R) (s : Fin states) : Transition R states := StateTransition.repeat p s

def Head.execute (prim : Syntax.StatePrimitives Φ σ) :
    Head S R → σ → StateTransition R σ
  | .exit i selected, s => .exit i selected s
  | .diverge, _ => .diverge
  | .request f arg next, s =>
    match prim f arg s with
    | .ret a t =>
      let reply := unpack (cast (congrArg Syntax.Payload (S.target f)) a)
      .repeat (next reply.1 reply.2) t
    | .fault t => .fault t
    | .diverge => .diverge

/-- Potential successful successors across the exhaustive typed reply list. -/
def Head.successors (replies : ReplyEnumeration S) : Head S R → List (Packet R)
  | .exit .. | .diverge => []
  | .request f _ next => (replies.packets f).map fun p => next p.1 p.2

/-- Inspect just the current block. The caller stays fixed and the incoming
value is read at its own label type. Every internal transfer consumes a reply. -/
def Table.head (g : Table S R) (caller : Syntax.Payload (R.get g.entry)) (config : Packet R) : Head S R :=
  match g.row config.1 with
  | .exit i => .exit i (g.selected i)
  | .diverge => .diverge
  | .request f arg next typed =>
    .request f (arg.eval ((g.bindings caller).push config.2)) fun j a =>
      ⟨next j, cast (congrArg Syntax.Payload (typed j).symm) a⟩

/-- Read at an exact typed configuration after checking the original CFG.
A local backedge does not require unfolding or a decreasing rank. -/
def Table.head? [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (caller : Syntax.Payload (R.get g.entry)) (config : Packet R) : Option (Head S R) :=
  if g.checkNative raw then some (g.head caller config) else none

def blockPoint (config : Packet R) (s : σ) :
    Feedback.Point R.length Unit σ :=
  .block config.1 config.2.val s

/-- The local native row still returns at a selected exit. Its separate
overlay continuation interprets that ordered exit as literal UB. -/
def StateTransition.routed : StateTransition R σ → Behaviour (R ++ Exits).length Unit σ
  | .exit i _ t => WithTop.some {Feedback.external R Exits (.ret i .unit t)}
  | .repeat config t => WithTop.some {Outcome.ret (Feedback.internal R Exits config.1) config.2.val t}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}

abbrev Transition.routed {states : Nat} : Transition R states → Behaviour (R ++ Exits).length Unit (Fin states) :=
  StateTransition.routed

/-- The installed native feedback graph with the caller bound. -/
noncomputable def Table.feedback (g : Table S R)
    (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.StatePrimitives Φ σ) :
    Feedback.Run R Exits Unit σ :=
  feedbackRun (.native g.entryRegion) (fun i => .native (g.blocks i)) (Syntax.model prim (g.bindings caller)).raw

/-- Apply the ordered selected-exit continuations to a classified result. -/
def Table.markExit {states : Nat} (g : Table S R) : Result 2 states → Result 2 states
  | .ret i t => if g.selected i then .ub else .ret i t
  | other => other

/-- Close native feedback at an exact block point and run the designated
exit continuation on a successful outward result. -/
noncomputable def Table.observeAt (g : Table S R)
    (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (config : Packet R) (s : σ) : Behaviour Exits.length Unit σ :=
  let M := (Syntax.model prim (g.bindings caller)).raw
  (Feedback.close (g.feedback caller prim) (blockPoint config s)).bind fun i a t =>
    Overlay.denote (CFG.Dependent.Native.exitContinuation (Γ := [R.get g.entry]) (L := Exits) (Φ := Φ) g.selected i) (extendModel M a) t

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
