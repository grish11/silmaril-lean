module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Renaming
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Named

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open CategoryTheory
open Comparison
open Silmaril.SSA.LambdaRTL.Institution (LawfulModel)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution (rtlMapClass ssaMapClass versionClass_map)

variable {V F F' F'' α : Type} [DecidableEq V] {a b c : Nat}

@[simp] theorem Graph.mapOp_id (graph : Graph V F a b) : graph.mapOp id = graph :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.mapOp_id graph

theorem Graph.mapOp_comp (h : F → F') (k : F' → F'') (graph : Graph V F a b) :
    graph.mapOp (k ∘ h) = (graph.mapOp h).mapOp k :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.mapOp_comp h k graph

/-- Primitive renaming preserves the wire identity on syntax. -/
theorem Graph.mapOp_identity (h : F → F') (a : Nat) :
    (Graph.identity (V := V) (F := F) a).mapOp h = Graph.identity a :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.mapOp_identity h a

/-- Primitive renaming commutes with the executable linker. The renaming
may identify primitive symbols. -/
theorem Graph.mapOp_link [Inhabited V] (h : F → F') (left : Graph V F a b) (right : Graph V F b c) :
    (left.link right).mapOp h = (left.mapOp h).link (right.mapOp h) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.mapOp_link h left right

theorem Graph.denote_mapOp (h : F → F') (model : Model F' Part α) (graph : Graph V F a b)
    (input : Fin a × α) :
    (graph.mapOp h).denote model input = graph.denote (model.reduct h) input :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.denote_mapOp h model graph input

/-- Rename primitives on observational arrow classes by reducing the model. -/
noncomputable def mapArrow (h : F → F') : Arrow V F α a b → Arrow V F' α a b :=
  Quotient.map (sa := graphSetoid (α := α)) (sb := graphSetoid (α := α)) (Graph.mapOp h)
    fun _ _ equal model input => by
      rw [Graph.denote_mapOp, Graph.denote_mapOp]
      exact equal (LawfulModel.reduct h model) input

theorem observe_mapArrow (h : F → F') (model : PairModel F' Part α)
    (arrow : Arrow V F α a b) (input : Fin a × α) :
    observe model (mapArrow h arrow) input = observe (LawfulModel.reduct h model) arrow input :=
  Quotient.inductionOn arrow fun graph => graph.denote_mapOp h model.val input

theorem sat_map_iff (h : F → F') (model : PairModel F' Part α) (lhs rhs : Arrow V F α a b) :
    Sat model (mapArrow h lhs) (mapArrow h rhs) ↔ Sat (LawfulModel.reduct h model) lhs rhs := by
  simp only [Sat, observe_mapArrow]

theorem mapArrow_mono (h : F → F') {lhs rhs : Arrow V F α a b} (refines : Refines lhs rhs) :
    Refines (mapArrow h lhs) (mapArrow h rhs) :=
  fun model => (sat_map_iff h model lhs rhs).mpr (refines (LawfulModel.reduct h model))

@[simp] theorem mapArrow_id (arrow : Arrow V F α a b) : mapArrow id arrow = arrow :=
  Quotient.inductionOn arrow fun graph => congrArg (Quotient.mk _) graph.mapOp_id

theorem mapArrow_comp (h : F → F') (k : F' → F'') (arrow : Arrow V F α a b) :
    mapArrow (k ∘ h) arrow = mapArrow k (mapArrow h arrow) :=
  Quotient.inductionOn arrow fun graph => congrArg (Quotient.mk _) (graph.mapOp_comp h k)

theorem mapArrow_identity (h : F → F') (a : Nat) :
    mapArrow h (identity (V := V) (α := α) a) = identity a :=
  congrArg (Quotient.mk _) (Graph.mapOp_identity h a)

variable [Inhabited V]

theorem mapArrow_compose (h : F → F') (left : Arrow V F α a b) (right : Arrow V F α b c) :
    mapArrow h (compose left right) = compose (mapArrow h left) (mapArrow h right) :=
  Quotient.inductionOn₂ left right fun first second =>
    congrArg (Quotient.mk _) (Graph.mapOp_link h first second)

/-- The primitive alphabet action as a functor of executable packet CFG classes. -/
noncomputable def renameFunctor (h : F → F') : Interface V F α ⥤ Interface V F' α where
  obj object := ⟨object.ports⟩
  map := mapArrow h
  map_id _ := mapArrow_identity h _
  map_comp left right := mapArrow_compose h left right

theorem Graph.namedRTL_closed (graph : Graph V F a b) (port : Fin a) :
    RoundTrip.PacketClosed (graph.namedRTL port) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Named.namedRTL_closed graph port

theorem Graph.namedRTL_observe (model : PairModel F Part α) (graph : Graph V F a b)
    (port : Fin a) (store : V → α) :
    rtlObserve model (graph.namedRTL port) store = publicResult <$> graph.denote model.val (port, store default) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Named.namedRTL_observe model graph port store

theorem Graph.namedRTL_mapOp (h : F → F') (graph : Graph V F a b) (port : Fin a) :
    (graph.mapOp h).namedRTL port = (graph.namedRTL port).mapOp h :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.namedRTL_mapOp h graph port

noncomputable def namedRTLClass (port : Fin a) : Arrow V F α a b → RTLClass V (NamedLabel b) F Part α :=
  Quotient.map (sa := graphSetoid (α := α)) (sb := rtlSetoid (M := Part) (α := α))
    (fun graph => graph.namedRTL port) fun _ _ equal model store => by
      rw [Graph.namedRTL_observe, Graph.namedRTL_observe, equal model (port, store default)]

/-- A packet arrow translates to a family of named SSA programs indexed by input port. -/
noncomputable def namedSSAClass (port : Fin a) (arrow : Arrow V F α a b) :
    SSAClass V (NamedLabel b) F Part α :=
  versionClass (namedRTLClass port arrow)

theorem namedRTLClass_mapArrow (h : F → F') (port : Fin a) (arrow : Arrow V F α a b) :
    namedRTLClass port (mapArrow h arrow) = rtlMapClass h (namedRTLClass port arrow) :=
  Quotient.inductionOn arrow fun graph => congrArg (Quotient.mk _) (graph.namedRTL_mapOp h port)

theorem namedSSAClass_mapArrow (h : F → F') (port : Fin a) (arrow : Arrow V F α a b) :
    namedSSAClass port (mapArrow h arrow) = ssaMapClass h (namedSSAClass port arrow) := by
  simp only [namedSSAClass, namedRTLClass_mapArrow, versionClass_map]

theorem namedRTLClass_observe (model : PairModel F Part α) (arrow : Arrow V F α a b)
    (port : Fin a) (store : V → α) :
    rtlClassObserve model (namedRTLClass port arrow) store = publicResult <$> observe model arrow (port, store default) :=
  Quotient.inductionOn arrow fun graph => graph.namedRTL_observe model port store

theorem namedSSAClass_observe (model : PairModel F Part α) (arrow : Arrow V F α a b)
    (port : Fin a) (store : V → α) :
    ssaClassObserve model (namedSSAClass port arrow) store = publicResult <$> observe model arrow (port, store default) :=
  (classObserve_version model _ store).trans (namedRTLClass_observe model arrow port store)

/-- The named SSA interpretation of a linked arrow uses the same staged
plugging rule. The right stage can start at any common external store
with its designated register set to the middle packet. -/
theorem namedSSA_compose_observe (model : PairModel F Part α) (left : Arrow V F α a b)
    (right : Arrow V F α b c) (port : Fin a) (store external : V → α) :
    ssaClassObserve model (namedSSAClass port (compose left right)) store =
      Cyclic.Institution.Refinement.plugSSA model (namedSSAClass port left) store (fun result =>
        match result.1 with
        | .inl _ => Part.none
        | .inr mid => ssaClassObserve model (namedSSAClass mid right) (upd external default result.2)) := by
  simp only [Cyclic.Institution.Refinement.plugSSA, namedSSAClass_observe, observe_compose,
    bind_map_left, map_bind]
  exact bind_congr fun _ => by simp [publicResult, upd]

/-- Packet refinement is exactly named RTL satisfaction at every input port. -/
theorem namedRTL_sat_iff (model : PairModel F Part α) (lhs rhs : Arrow V F α a b) :
    (∀ port, Cyclic.Institution.Refinement.rtlSat model (namedRTLClass port lhs) (namedRTLClass port rhs)) ↔
      Sat model lhs rhs := by
  change (∀ port store, rtlClassObserve model (namedRTLClass port lhs) store ≤
      rtlClassObserve model (namedRTLClass port rhs) store) ↔ Sat model lhs rhs
  simp only [namedRTLClass_observe, Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Named.publicResult_le_iff]
  exact ⟨fun h input => h input.1 (fun _ => input.2), fun h port store => h (port, store default)⟩

/-- Packet refinement is exactly the existing named SSA satisfaction at every input port. -/
theorem namedSSA_sat_iff (model : PairModel F Part α) (lhs rhs : Arrow V F α a b) :
    (∀ port, Cyclic.Institution.Refinement.ssaSat model (namedSSAClass port lhs) (namedSSAClass port rhs)) ↔
      Sat model lhs rhs :=
  (forall_congr' fun port => Cyclic.Institution.Refinement.ssaSat_version_iff model
    (namedRTLClass port lhs) (namedRTLClass port rhs)).trans (namedRTL_sat_iff model lhs rhs)

theorem namedSSA_refines_iff (lhs rhs : Arrow V F α a b) :
    (∀ port, Cyclic.Institution.Refinement.ssaRefines (namedSSAClass port lhs) (namedSSAClass port rhs)) ↔
      Refines lhs rhs :=
  ⟨fun holds model => (namedSSA_sat_iff model lhs rhs).mp (fun port => holds port model),
    fun refines port model => (namedSSA_sat_iff model lhs rhs).mpr (refines model) port⟩

/-- The named versioning comparison stays in the packet interpretation on classes. -/
@[simp] theorem deversion_namedSSAClass [Infinite V] (port : Fin a) (arrow : Arrow V F α a b) :
    deversionClass (namedSSAClass port arrow) = namedRTLClass port arrow :=
  deversion_version_class _

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
