module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Proofs

open CategoryTheory
open RVSDG (Tuple)
open SeaOfNodes.Loop (Incoming)
open Memory.Diamond.Institution (PortMap pullInput pullInput_get reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

set_option backward.isDefEq.respectTransparency false

variable {P Q R : EntrySignature} {cells : Nat}

private theorem lift_id (P : EntrySignature) :
    liftAddress (𝟙 P) = 𝟙 (⟨.address :: P.args⟩ : EntrySignature) := by
  apply congrArg EntrySignature.Hom.mk
  funext sort p
  cases p <;> rfl

private theorem lift_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    liftAddress (h ≫ k) = liftAddress h ≫ liftAddress k := by
  apply congrArg EntrySignature.Hom.mk
  funext sort p
  cases p <;> rfl

theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph := by
  cases graph
  simp [mapGraph, lift_id]
  exact ⟨rfl, rfl⟩

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) := by
  simp only [mapGraph, lift_comp, Loop.Institution.mapGraph_comp]
  rfl

private theorem pull_tail {source target : List ValueSort} (rename : PortMap source target)
    (address : Address cells) (input : Tuple (Val cells) target) :
    pullInput (fun p => .tail (rename p)) (.cons (F := Val cells) (t := .address) address input) =
      pullInput rename input := by
  induction source with
  | nil => rfl
  | cons _ _ ih =>
    simp only [pullInput, ih]
    rfl

theorem step_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (arrival : Incoming) (heap : Heap model.cells) :
    (mapGraph h graph).step model.input arrival heap = graph.step (reduct h model).input arrival heap := by
  let extended : EntryModel ⟨.address :: Q.args⟩ :=
    ⟨model.cells, (mapGraph h graph).operands model.input arrival⟩
  have pulled : (reduct (liftAddress h) extended).input = graph.operands (reduct h model).input arrival := by
    cases arrival <;>
      simp only [extended, reduct, pullInput, liftAddress, Graph.operands, mapGraph, Incoming.select,
        Tuple.get, pull_tail, pullInput_get]
  exact (Loop.Institution.step_mapGraph (liftAddress h) graph.activation extended heap).trans
    (congrArg (fun input => graph.activation.step input heap) pulled)

theorem evalWithin_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (budget : Nat) (arrival : Incoming) (heap : Heap model.cells) :
    (mapGraph h graph).evalWithin model.input budget arrival heap =
      graph.evalWithin (reduct h model).input budget arrival heap := by
  induction budget generalizing arrival heap with
  | zero =>
    simp only [Graph.evalWithin, step_mapGraph]
    rfl
  | succ budget ih =>
    simp only [Graph.evalWithin, step_mapGraph]
    cases graph.step (reduct h model).input arrival heap with
    | inl _ => rfl
    | inr next => exact ih .backedge next

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Proofs
