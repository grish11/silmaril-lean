module

public import Mathlib.Data.List.Dedup
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.State.Defs

/-! # Finite guarded runs over arbitrary state types -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet unpack)
open TwoRequest (Exits Tag)
open Syntax (Payload StateReply StatePrimitives)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty}
  {σ : Type v} {τ : Type w}

/-- One typed query and its whole deterministic answer on the original carrier. -/
structure RunRow (Φ : Type u) [HasTy Φ Syntax.Ty] (σ : Type v) where
  op : Φ
  arg : Payload (instrSrc op)
  incoming : σ
  answer : StateReply (instrTrg op) σ

def RunRow.returned? (r : RunRow Φ σ) : Option σ :=
  match r.answer with
  | .ret _ s | .fault s => some s
  | .diverge => none

inductive RunStop (σ : Type v) where
  | exit (tag : Tag) (selected : Bool) (final : σ)
  | fault (final : σ)
  | diverge

def RunStop.final? : RunStop σ → Option σ
  | .exit _ _ s | .fault s => some s
  | .diverge => none

def RunStop.mapState (f : σ → τ) : RunStop σ → RunStop τ
  | .exit i selected s => .exit i selected (f s)
  | .fault s => .fault (f s)
  | .diverge => .diverge

def RunStop.behaviour : RunStop σ → Behaviour Exits.length Unit σ
  | .exit i selected s => if selected then ⊤ else WithTop.some {Outcome.ret i .unit s}
  | .fault s => WithTop.some {Outcome.fault s}
  | .diverge => WithTop.some {Outcome.diverge}

def replyDestination (f : Φ) (next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R)
    (value : Payload (instrTrg f)) : Packet R :=
  let packet := unpack (cast (congrArg Payload (S.target f)) value)
  next packet.1 packet.2

/-- A finite observation derivation follows actual typed heads and replies.
An ordinary-divergence head records no query. A primitive divergence
records its answer. Both stop the normalized derivation. -/
inductive FiniteRun (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) :
    Packet R → σ → List (RunRow Φ σ) → RunStop σ → Prop where
  | exit {p s i selected} (head : g.head caller p = .exit i selected) :
      FiniteRun g caller prim p s [] (.exit i selected s)
  | silent {p s} (head : g.head caller p = .diverge) :
      FiniteRun g caller prim p s [] .diverge
  | «repeat» {p s f arg next value t rows stop}
      (head : g.head caller p = .request f arg next) (answer : prim f arg s = .ret value t)
      (tail : FiniteRun g caller prim (replyDestination f next value) t rows stop) :
      FiniteRun g caller prim p s (⟨f, arg, s, .ret value t⟩ :: rows) stop
  | fault {p s f arg next t} (head : g.head caller p = .request f arg next)
      (answer : prim f arg s = .fault t) :
      FiniteRun g caller prim p s [⟨f, arg, s, .fault t⟩] (.fault t)
  | diverge {p s f arg next} (head : g.head caller p = .request f arg next)
      (answer : prim f arg s = .diverge) :
      FiniteRun g caller prim p s [⟨f, arg, s, .diverge⟩] .diverge

/-- The deduplicated list of states is taken from the shared start and the
success and fault answers. The embedding keeps exact final-state equality. -/
structure RunSupport (σ : Type v) (initial : σ) where
  values : List σ
  distinct : values.Nodup
  initial_mem : initial ∈ values

def RunSupport.ofRows [DecidableEq σ] (initial : σ) (rows : List (RunRow Φ σ)) : RunSupport σ initial :=
  let values := initial :: rows.filterMap RunRow.returned?
  ⟨values.dedup, List.nodup_dedup values, List.mem_dedup.mpr (List.mem_cons_self ..)⟩

variable {initial : σ}

def RunSupport.embed (support : RunSupport σ initial) : Fin support.values.length ↪ σ :=
  ⟨support.values.get, support.distinct.injective_get⟩

/-- Off support, encode at the initial state. Replay only uses the
inverse equation for states proved to occur in the finite runs. -/
def RunSupport.code [DecidableEq σ] (support : RunSupport σ initial) (s : σ) :
    Fin support.values.length :=
  if h : s ∈ support.values then ⟨support.values.idxOf s, List.idxOf_lt_length_of_mem h⟩
  else ⟨support.values.idxOf initial, List.idxOf_lt_length_of_mem support.initial_mem⟩

def RunRow.encode [DecidableEq σ] (support : RunSupport σ initial) (r : RunRow Φ σ) :
    InterpreterScript.Row Φ support.values.length :=
  ⟨⟨r.op, r.arg, support.code r.incoming⟩, r.answer.mapState support.code⟩

/-- A total interpreter on the coded carrier used to establish consistency
of the recorded script. The executable witness itself uses script lookup. -/
def RunSupport.restrict [DecidableEq σ] (support : RunSupport σ initial) (prim : StatePrimitives Φ σ) :
    Syntax.Primitives Φ support.values.length :=
  fun f a s => (prim f a (support.embed s)).mapState support.code

/-- Reconstruct one concrete interpreter from both finite derivations. -/
def RunSupport.witness {A : Syntax.Ty} [DecidableEq σ] (support : RunSupport σ initial)
    (input : Payload A) (rows : List (RunRow Φ σ)) : EntryCounterexample Φ A support.values.length :=
  ⟨input, support.code initial, rows.map (RunRow.encode support)⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
