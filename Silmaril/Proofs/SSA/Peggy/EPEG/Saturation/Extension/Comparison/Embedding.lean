module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Defs
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms
import Mathlib.Data.Fintype.Card

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ts : List (Ty Data)} {n k j l : Nat}
variable {small : State P params results n l} {large : State P params results k l}
variable {larger : State P params results j l}
variable {a : Fin n → Ty Data} {b : Fin k → Ty Data} {c : Fin j → Ty Data}

private theorem tuple_identity (args : Tuple (Ref a) ts) :
    (VertexMap.identity a).tuple args = args := by
  induction args with
  | nil => rfl
  | cons r rs ih => exact congrArg (Tuple.cons r) ih

private theorem tuple_comp (f : VertexMap a b) (g : VertexMap b c) (args : Tuple (Ref a) ts) :
    (g.comp f).tuple args = g.tuple (f.tuple args) := by
  induction args with
  | nil => rfl
  | cons r rs ih => exact congrArg (Tuple.cons ((g.comp f).ref r)) ih

private theorem node_identity {t : Ty Data} (row : Node P params (Fin l) a t) :
    (VertexMap.identity a).node row = row := by
  cases row
  simp only [VertexMap.node, Node.ofLabel, tuple_identity]

private theorem node_comp (f : VertexMap a b) (g : VertexMap b c) {t : Ty Data}
    (row : Node P params (Fin l) a t) :
    (g.comp f).node row = g.node (f.node row) :=
  congrArg (Node.ofLabel row.label) (tuple_comp f g row.args)

def refl (state : State P params results n l) : Embedding state state where
  vertices := VertexMap.identity _
  rows i := heq_of_eq (node_identity (state.graph.node i)).symm
  roots := (tuple_identity _).symm
  forest := rfl
  classes _ _ := id

def trans (first : Embedding small large) (second : Embedding large larger) :
    Embedding small larger where
  vertices := second.vertices.comp first.vertices
  rows i :=
    (second.rows (first.vertices.address i)).trans
      ((second.vertices.node_heq (first.vertices.sort_eq i) (first.rows i)).trans
        (heq_of_eq (node_comp first.vertices second.vertices (small.graph.node i)).symm))
  roots := by rw [second.roots, first.roots, tuple_comp]
  forest := second.forest.trans first.forest
  classes a b h := second.classes _ _ (first.classes a b h)

theorem refl_address (state : State P params results n l) (i : Fin n) :
    (refl state).vertices.address i = i := by unfold refl; rfl

theorem trans_address (first : Embedding small large) (second : Embedding large larger) (i : Fin n) :
    (trans first second).vertices.address i = second.vertices.address (first.vertices.address i) := by
  unfold trans
  rfl

theorem append_address_old (e : Embedding small large) (row : Row small.graph) (i : Fin n) :
    (e.appendVertices row).address i.castSucc = (e.vertices.address i).castSucc := by
  simp [Embedding.appendVertices]

theorem append_address_fresh (e : Embedding small large) (row : Row small.graph) :
    (e.appendVertices row).address (Fin.last n) = Fin.last k := by
  simp [Embedding.appendVertices]

private theorem append_comp (e : Embedding small large) (row : Row small.graph) :
    (e.mapRow row).vertices.comp e.vertices = (e.appendVertices row).comp row.vertices := by
  suffices same : ((e.mapRow row).vertices.comp e.vertices).address =
      ((e.appendVertices row).comp row.vertices).address by
    generalize (e.mapRow row).vertices.comp e.vertices = f at *
    generalize (e.appendVertices row).comp row.vertices = g at *
    cases f
    cases g
    cases same
    rfl
  ext i
  exact congrArg Fin.val (append_address_old e row i).symm

@[expose] def append (e : Embedding small large) (row : Row small.graph)
    (cs : Classes (n + 1)) (ds : Classes (k + 1))
    (joined : ∀ a b, cs a = cs b →
      ds ((e.appendVertices row).address a) = ds ((e.appendVertices row).address b)) :
    Embedding (⟨row.append, cs⟩ : State P params results (n + 1) l)
      (⟨(e.mapRow row).append, ds⟩ : State P params results (k + 1) l) where
  vertices := e.appendVertices row
  rows i := by
    induction i using Fin.lastCases with
    | last =>
      change HEq ((e.mapRow row).append.node ((e.appendVertices row).address (Fin.last n)))
        ((e.appendVertices row).node (row.append.node (Fin.last n)))
      rw [append_address_fresh]
      refine ((e.mapRow row).node_fresh).trans ?_
      refine HEq.trans ?_ ((e.appendVertices row).node_heq row.sort_fresh row.node_fresh).symm
      apply heq_of_eq
      change Node.ofLabel row.label ((e.mapRow row).vertices.tuple (e.vertices.tuple row.args)) =
        Node.ofLabel row.label ((e.appendVertices row).tuple (row.vertices.tuple row.args))
      rw [← tuple_comp, ← tuple_comp, append_comp]
    | cast i =>
      change HEq ((e.mapRow row).append.node ((e.appendVertices row).address i.castSucc))
        ((e.appendVertices row).node (row.append.node i.castSucc))
      rw [append_address_old]
      refine ((e.mapRow row).node_old (e.vertices.address i)).trans ?_
      refine ((e.mapRow row).vertices.node_heq (e.vertices.sort_eq i) (e.rows i)).trans ?_
      refine HEq.trans ?_ ((e.appendVertices row).node_heq (row.sort_old i) (row.node_old i)).symm
      apply heq_of_eq
      change (e.mapRow row).vertices.node (e.vertices.node (small.graph.node i)) =
        (e.appendVertices row).node (row.vertices.node (small.graph.node i))
      rw [← node_comp, ← node_comp, append_comp]
  roots := by
    change (e.mapRow row).vertices.tuple large.graph.roots =
      (e.appendVertices row).tuple (row.vertices.tuple small.graph.roots)
    rw [e.roots, ← tuple_comp, ← tuple_comp, append_comp]
  forest := e.forest
  classes := joined

theorem append_address (e : Embedding small large) (row : Row small.graph)
    (cs : Classes (n + 1)) (ds : Classes (k + 1))
    (joined : ∀ a b, cs a = cs b →
      ds ((e.appendVertices row).address a) = ds ((e.appendVertices row).address b))
    (i : Fin (n + 1)) : (append e row cs ds joined).vertices.address i =
      (e.appendVertices row).address i := rfl

def step (receipt : Step small) : Embedding small receipt.apply where
  vertices := receipt.row.vertices
  rows := receipt.row.node_old
  roots := rfl
  forest := rfl
  classes _ _ := receipt.extends

theorem step_address (receipt : Step small) (i : Fin n) :
    (step receipt).vertices.address i = i.castSucc := by unfold step; rfl

theorem step_vertices (receipt : Step small) : (step receipt).vertices = receipt.row.vertices := by
  unfold step
  rfl

theorem embedding_size_le (e : Embedding small large) : n ≤ k := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective e.vertices.address e.vertices.address.injective

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison
