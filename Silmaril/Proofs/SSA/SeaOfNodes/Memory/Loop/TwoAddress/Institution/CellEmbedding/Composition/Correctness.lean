module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbeddingProofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Silmaril.MLIR.MemRef (Buffer)
open CellEmbedding (Embedding extend restrict SameFrame)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution (PortMap pullInput reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {small middle large : Nat} {P Q : EntrySignature}

set_option backward.isDefEq.respectTransparency false

theorem pullInput_embed {args target : List ValueSort} (rename : PortMap args target)
    (e : Embedding small large) (inputs : Tuple (Val small) target) :
    pullInput rename (CellEmbedding.input e inputs) = CellEmbedding.input e (pullInput rename inputs) := by
  induction args with
  | nil => rfl
  | cons sort tail ih =>
    change Tuple.cons ((CellEmbedding.input e inputs).get (rename .head))
      (pullInput (fun p => rename (.tail p)) (CellEmbedding.input e inputs)) = _
    rw [CellEmbedding.input_get, ih]
    rfl

theorem reduct_embed (h : P ⟶ Q) (model : EntryModel Q) (e : Embedding model.cells large) :
    reduct h (embedModel model e) = embedModel (reduct h model) e :=
  congrArg (fun inputs => (⟨large, inputs⟩ : EntryModel P))
    (pullInput_embed (EntrySignature.Hom.port h) e model.input)

theorem embedModel_trans (model : EntryModel Q) (e : Embedding model.cells middle)
    (f : Embedding middle large) :
    embedModel model (e.trans f) = embedModel (embedModel model e) f :=
  congrArg (fun inputs => (⟨large, inputs⟩ : EntryModel Q)) (CellEmbedding.input_trans e f model.input)

theorem embedOutput_trans (e : Embedding small middle) (f : Embedding middle large)
    (inner : Heap middle) (outer : Heap large) :
    embedOutput (e.trans f) (extend f outer inner) =
      embedOutput f outer ∘ embedOutput e inner := by
  funext raw
  obtain ⟨⟨word, final⟩, rfl⟩ := (runtimeResult small).surjective raw
  change embedOutput (e.trans f) (extend f outer inner) (encodeResult word final) =
    embedOutput f outer (embedOutput e inner (encodeResult word final))
  rw [embedOutput_encode, embedOutput_encode, embedOutput_encode, CellEmbedding.extend_trans]

theorem observe_map_embed_trans (h : P ⟶ Q) (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel Q)
    (e : Embedding model.cells middle) (f : Embedding middle large) (initial : Heap large) :
    (p.map h).observe (embedModel model (e.trans f)) initial =
      (((p.observe (reduct h model) (restrict e (restrict f initial))).map
        (embedOutput e (restrict f initial))).map (embedOutput f initial)) := by
  rw [p.observe_map h]
  change p.observe ⟨large, pullInput (EntrySignature.Hom.port h) (CellEmbedding.input (e.trans f) model.input)⟩
    initial = _
  rw [pullInput_embed]
  change p.observe (embedModel (reduct h model) (e.trans f)) initial = _
  rw [p.observe_embed, CellEmbedding.restrict_trans, Part.map_map]
  have composition := embedOutput_trans e f (restrict f initial) initial
  rw [CellEmbedding.extend_restrict] at composition
  rw [composition]

theorem memRef_returns_map_embed_trans_iff (h : P ⟶ Q) (p : MemRefRoom.GeneratedProgram P.args)
    (model : EntryModel Q) (e : Embedding model.cells middle) (f : Embedding middle large)
    (initial : Buffer large) (word : Word) (final : Buffer large) :
    (MemRefRoom.GeneratedProgram.lower (mapGraph h p.source)).Returns (embedModel model (e.trans f))
        initial (word, final) ↔
      p.Returns (reduct h model) ⟨restrict e (restrict f initial.cell)⟩ (word, ⟨restrict e (restrict f final.cell)⟩) ∧
        SameFrame f initial.cell final.cell ∧ SameFrame e (restrict f initial.cell) (restrict f final.cell) := by
  rw [MemRefRoom.GeneratedProgram.returns_iff_native]
  change nativeReturns (mapGraph h p.source) (embedModel model (e.trans f)) initial.cell word final.cell ↔ _
  rw [nativeReturns_mapGraph]
  change nativeReturns p.source
    ⟨large, pullInput (EntrySignature.Hom.port h) (CellEmbedding.input (e.trans f) model.input)⟩
    initial.cell word final.cell ↔ _
  rw [pullInput_embed]
  change nativeReturns p.source (embedModel (reduct h model) (e.trans f)) initial.cell word final.cell ↔ _
  rw [nativeReturns_embed_iff, CellEmbedding.restrict_trans,
    CellEmbedding.restrict_trans, CellEmbedding.sameFrame_trans, ← p.returns_iff_native]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbeddingProofs
