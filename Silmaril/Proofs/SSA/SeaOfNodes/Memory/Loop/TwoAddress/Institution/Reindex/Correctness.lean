module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Proofs

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution (PortMap pullInput pullInput_get reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CarriedAddress.Institution (liftAddress)

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
  have lifted : liftAddresses (𝟙 P) = 𝟙 (⟨activationArgs P.args⟩ : EntrySignature) := by
    apply (congrArg liftAddress (lift_id P)).trans
    exact lift_id _
  cases graph
  simp only [mapGraph, lifted, Loop.Institution.mapGraph_id]
  rfl

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) := by
  have lifted : liftAddresses (h ≫ k) = liftAddresses h ≫ liftAddresses k :=
    (congrArg liftAddress (lift_comp h k)).trans (lift_comp _ _)
  simp only [mapGraph, lifted, Loop.Institution.mapGraph_comp]
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

private theorem seed_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (heap : Heap model.cells) :
    (mapGraph h graph).seed model.input heap = graph.seed (reduct h model).input heap := by
  simp only [Graph.seed, mapGraph, reduct, pullInput_get]

theorem pull_operands (h : P ⟶ Q) (model : EntryModel Q) (header : Header model.cells) :
    pullInput (liftAddresses h).port (header.operands model.input) = header.operands (reduct h model).input := by
  simp only [reduct, Header.operands, pullInput, liftAddresses, liftAddress, Tuple.get, pull_tail]
  rfl

private theorem feedback_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (header : Header model.cells) (heap : Heap model.cells) :
    (mapGraph h graph).feedback model.input header heap =
      graph.feedback (reduct h model).input header heap := by
  have atPort (p : Port (activationArgs P.args) .address) :
      (header.operands model.input).get ((liftAddresses h).port p) =
        (header.operands (reduct h model).input).get p :=
    (pullInput_get (liftAddresses h).port (header.operands model.input) p).symm.trans
      (congrArg (·.get p) (pull_operands h model header))
  simp only [Graph.feedback, mapGraph, atPort]

theorem step_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (header : Header model.cells) :
    (mapGraph h graph).step model.input header = graph.step (reduct h model).input header := by
  let extended : EntryModel ⟨activationArgs Q.args⟩ := ⟨model.cells, header.operands model.input⟩
  have step := (Loop.Institution.step_mapGraph (liftAddresses h) graph.activation extended header.heap).trans
    (congrArg (fun input => graph.activation.step input header.heap) (pull_operands h model header))
  exact congrArg₂ (fun result feedback => Sum.map id feedback result) step
    (funext (feedback_map h graph model header))

private theorem evalWithin_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (budget : Nat) (header : Header model.cells) :
    (mapGraph h graph).evalWithin model.input budget header =
      graph.evalWithin (reduct h model).input budget header := by
  induction budget generalizing header with
  | zero =>
    simp only [Graph.evalWithin, step_mapGraph]
    rfl
  | succ budget ih =>
    simp only [Graph.evalWithin, step_mapGraph]
    cases graph.step (reduct h model).input header with
    | inl _ => rfl
    | inr next => exact ih next

theorem nativeReturns_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    nativeReturns (mapGraph h graph) model initial word final ↔
      nativeReturns graph (reduct h model) initial word final := by
  simp only [nativeReturns, Graph.Returns, seed_map, evalWithin_mapGraph]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Proofs
