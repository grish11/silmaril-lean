module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Institution.Satisfaction

/-! # Exact satisfaction for deterministic packed dispatcher models -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Category.FiniteIteration hiding Table
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives model)
open TwoRequest (Exits)
open CategoryTheory (Discrete)
open Institution.Observational (lambdaSSA)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {A : Syntax.Ty} {L : List Syntax.Ty}

/-- Both rebindings preserve the actual primitive relations. The sole
ambient bound value is the endpoint's decoding of the shared caller. -/
theorem CodedModel.atEntry_agrees (M : CodedModel.{u,v} Φ A) (e : CodedEntry Φ A L) :
    (M.atEntry e).instr = M.raw.instr ∧ (M.atEntry e).faults = M.raw.faults ∧
      (M.atEntry e).prim = M.raw.prim ∧ (M.atEntry e).bound 0 = (e.decode M.caller).val :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Satisfaction of an overlay refinement sentence is the installed
pointwise lifted observation order under the coded entry bindings. -/
theorem CodedModel.sat_le_iff (M : CodedModel.{u,v} Φ A) (e f : CodedEntry Φ A L) :
    M.Sat (.le e f) ↔
      ∀ s : M.store, Overlay.denote e.region (M.atEntry e) s ≤ Overlay.denote f.region (M.atEntry f) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution.sat_le_iff
    M e f

/-- Native atoms always produce ordinary behaviours, so a native sentence
cannot represent an endpoint at a state where its decoration exposes top. -/
theorem CodedModel.native_ne_top (M : CodedModel.{u,v} Φ A) (e : CodedEntry Φ A L)
    (r : CFG.Dependent.Native.Typed Φ [e.capture] L) (s : M.store) :
    Overlay.denote (.native r) (M.atEntry e) s ≠ ⊤ :=
  WithTop.coe_ne_top

/-- With identity capture bindings and all exits forwarded, satisfaction
is exactly satisfaction in the installed native LambdaSSA room. -/
theorem CodedModel.sat_native_iff (M : CodedModel.{u,v} Φ A) (r t : CFG.Dependent.Native.Typed Φ [A] L) :
    M.Sat (.le ⟨A, id, withExitUB r (fun _ => false)⟩ ⟨A, id, withExitUB t (fun _ => false)⟩) ↔
      ((lambdaSSA.{u,0,v} Φ L.length).room [A].length).Sat (Discrete.mk M.raw)
        (.le ⟨r.val, r.property.scoped⟩ ⟨t.val, t.property.scoped⟩) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution.sat_native_iff
    M r t

variable {S : RequestSignature Φ} {R T : List Syntax.Ty} {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}

theorem CodedModel.sat_refinement_iff (M : CodedModel.{u,v} Φ A) :
    M.Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) ↔
      ∀ s : M.store,
        Shape.denote (withExitUB raw g.selected) (model M.handler (g.visible.bindings (decodeLeft M.caller))) s ≤
          Shape.denote (withExitUB raw' h.selected) (model M.handler (h.visible.bindings (decodeRight M.caller))) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution.sat_refinement_iff
    M

variable [DecidableEq Φ] {callers : CallerEnumeration A} {replies : ReplyEnumeration S}
  {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

/-- Exact readback gates validity over the deterministic graph models
with atomic carrier Unit and any store type at universe v. -/
theorem Table.checkEntries_satisfies_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ M : CodedModel.{u,v} Φ A, M.Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution.accepts_satisfies_iff
    checked checked'

/-- The computed finite carrier suffices for validity in the supported
model class. -/
theorem Table.checkEntries_cutoff_satisfies_iff (checked : g.checkNative raw = true)
    (checked' : h.checkNative raw' = true) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ (input : Payload A) (handler : Primitives Φ n),
        (CodedModel.mk (Fin n) input handler).Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution.cutoff_satisfies_iff
    checked checked'

/-- A negative verdict supplies a supported finite model witnessing failed
satisfaction of the original decorated sentence. -/
theorem Table.checkEntries_countermodel
    (rejected : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    ∃ (input : Payload A) (handler : Primitives Φ n),
      ¬ (CodedModel.mk (Fin n) input handler).Sat (g.refinementSentence h raw raw' decodeLeft decodeRight) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Institution.countermodel
    rejected

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
