module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Thms

/-! # Observational sentences for coded packed overlay entries -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Category.FiniteIteration hiding Table
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives emptyBindings model)
open TwoRequest (Exits)
open Silmaril.Logic.Institution.Observational (Sentence)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {A : Syntax.Ty} {L : List Syntax.Ty}

/-- An original typed region with a decoder from the shared caller type
to its own captured entry packet. -/
structure CodedEntry (Φ : Type u) [HasTy Φ Syntax.Ty] (A : Syntax.Ty) (L : List Syntax.Ty) where
  capture : Syntax.Ty
  decode : Payload A → Payload capture
  region : Overlay.Region Φ [capture] L

/-- A presentation of the supported observational models. Their atomic
carrier is Unit. The success, fault and primitive-divergence relations
are exactly the graph of this total typed deterministic handler. -/
structure CodedModel (Φ : Type u) [HasTy Φ Syntax.Ty] (A : Syntax.Ty) where
  store : Type v
  caller : Payload A
  handler : StatePrimitives Φ store

def CodedModel.raw (M : CodedModel.{u,v} Φ A) : Institution.Observational.Model.{u,0,v} Φ 1 :=
  (model M.handler (emptyBindings.push M.caller)).raw

/-- Rebind only the captured value of the existing observational model.
Both endpoint models use the same handler and machine-state carrier. -/
def CodedModel.atEntry (M : CodedModel.{u,v} Φ A) (e : CodedEntry Φ A L) :
    Institution.Observational.Model.{u,0,v} Φ 1 :=
  { M.raw with bound := fun i => (emptyBindings.push (e.decode M.caller) i).val }

/-- The extra observation records fresh top separately from ordinary outcomes. -/
def observesOutcome {n : Nat} {σ : Type v} (p : Behaviour n Unit σ) : Option (Outcome n Unit σ) → Prop
  | none => p = ⊤
  | some out => out ∈ p.possible

/-- Each observation also retains the initial machine state. -/
def CodedModel.observations (M : CodedModel.{u,v} Φ A) (e : CodedEntry Φ A L) :
    Set (M.store × Option (Outcome L.length Unit M.store)) :=
  {o | observesOutcome (Overlay.denote e.region (M.atEntry e) o.1) o.2}

/-- Reuse the observational sentence's inclusion and equality semantics
with a behaviour assignment that reflects the lifted overlay order. -/
def CodedModel.Sat (M : CodedModel.{u,v} Φ A) (φ : Sentence (CodedEntry Φ A L)) : Prop :=
  φ.Holds M.observations

variable {S : RequestSignature Φ} {R T : List Syntax.Ty}

/-- Both subjects retain the original typed packed CFG and its exact
selected-exit continuations. The shared caller may decode differently. -/
def Table.refinementSentence (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (decodeLeft : Payload A → Payload (R.get g.entry))
    (decodeRight : Payload A → Payload (T.get h.entry)) : Sentence (CodedEntry Φ A Exits) :=
  .le ⟨_, decodeLeft, withExitUB raw g.selected⟩ ⟨_, decodeRight, withExitUB raw' h.selected⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
