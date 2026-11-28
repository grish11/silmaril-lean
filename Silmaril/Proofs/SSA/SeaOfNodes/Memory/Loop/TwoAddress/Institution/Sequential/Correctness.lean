module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Proofs

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open CellEmbedding (Embedding DisjointImages extend restrict result)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {cells leftCells rightCells : Nat} {P Q : EntrySignature}

set_option backward.isDefEq.respectTransparency false

theorem observe_eq_some_iff (first : Stage cells) (second : Word → Stage cells) (initial : Heap cells)
    (word nextWord : Word) (final : Heap cells) :
    observe first second initial = Part.some (word, nextWord, final) ↔
      ∃ middle, first initial = Part.some (word, middle) ∧ second word middle = Part.some (nextWord, final) := by
  simp only [observe, Part.eq_some_iff, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨⟨w, middle⟩, firstReturn, ⟨v, next⟩, secondReturn, equal⟩
    cases equal
    exact ⟨middle, firstReturn, secondReturn⟩
  · rintro ⟨middle, firstReturn, secondReturn⟩
    exact ⟨(word, middle), firstReturn, (nextWord, final), secondReturn, rfl⟩

private theorem bind_map_eq_none_iff {α β γ : Type} (first : Part α) (second : α → Part β)
    (finish : α → β → γ) :
    (first.bind fun a => (second a).map (finish a)) = Part.none ↔
      first = Part.none ∨ ∃ a, first = Part.some a ∧ second a = Part.none := by
  rcases Part.eq_none_or_eq_some first with absent | ⟨a, returned⟩
  · simp [absent]
  · rw [returned, Part.bind_some, Part.eq_none_iff']
    change (¬ (second a).Dom) ↔ Part.some a = Part.none ∨
      ∃ b, Part.some a = Part.some b ∧ second b = Part.none
    simp only [Part.some_ne_none, false_or, Part.some_inj]
    constructor
    · intro absent
      exact ⟨a, rfl, Part.eq_none_iff'.mpr absent⟩
    · rintro ⟨_, rfl, absent⟩
      exact Part.eq_none_iff'.mp absent

theorem observe_eq_none_iff (first : Stage cells) (second : Word → Stage cells) (initial : Heap cells) :
    observe first second initial = Part.none ↔
      first initial = Part.none ∨
        ∃ word middle, first initial = Part.some (word, middle) ∧ second word middle = Part.none := by
  simpa only [observe, Prod.exists] using
    bind_map_eq_none_iff (first initial) (fun out => second out.1 out.2)
      (fun out next => (out.1, next.1, next.2))

theorem localObserve_eq_none_iff (e : Embedding leftCells cells) (f : Embedding rightCells cells)
    (left : Stage leftCells) (right : Word → Stage rightCells) (initial : Heap cells) :
    localObserve e f left right initial = Part.none ↔
      left (restrict e initial) = Part.none ∨
        ∃ word leftFinal, left (restrict e initial) = Part.some (word, leftFinal) ∧
          right word (restrict f initial) = Part.none := by
  simpa only [localObserve, Prod.exists] using
    bind_map_eq_none_iff (left (restrict e initial)) (fun out => right out.1 (restrict f initial))
      (fun out next => (out.1, next.1, extend f (extend e initial out.2) next.2))

/-- Factor a pipeline as soon as both stage observers obey the ordinary
heap-extension law. The second call still receives the first returned word. -/
theorem observe_eq_local (e : Embedding leftCells cells) (f : Embedding rightCells cells)
    (disjoint : DisjointImages e f) (first : Stage cells) (second : Word → Stage cells)
    (left : Stage leftCells) (right : Word → Stage rightCells)
    (firstFrame : ∀ heap, first heap = (left (restrict e heap)).map (result e heap))
    (secondFrame : ∀ word heap, second word heap = (right word (restrict f heap)).map (result f heap))
    (initial : Heap cells) :
    observe first second initial = localObserve e f left right initial := by
  rw [observe, firstFrame, Part.bind_map, localObserve]
  congr 1
  funext out
  obtain ⟨word, leftFinal⟩ := out
  change (second word (extend e initial leftFinal)).map (fun (w, final) => (word, w, final)) = _
  rw [secondFrame, Part.map_map, CellEmbedding.restrict_extend_disjoint e f disjoint]
  rfl

theorem numberedStage_embed (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (e : Embedding model.cells cells) (initial : Heap cells) :
    numberedStage p (embedModel model e) initial =
      (numberedStage p model (restrict e initial)).map (result e initial) := by
  unfold numberedStage
  rw [p.observe_embed, Part.map_map, Part.map_map]
  simp only [embedModel, embedOutput, Function.comp_def, Equiv.symm_apply_apply]

theorem colouredStage_eq_numbered (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P) :
    colouredStage p model = numberedStage p model := by
  funext initial
  rw [colouredStage, p.petriObserve_eq_numbered, numberedStage]

private theorem decode_eq_some_iff (observed : Part (Tuple (WireVal cells) (Threaded wordPorts)))
    (word : Word) (heap : Heap cells) :
    observed.map (runtimeResult cells).symm = Part.some (word, heap) ↔
      observed = Part.some (encodeResult word heap) := by
  let codec := runtimeResult cells
  change observed.map codec.symm = Part.some (word, heap) ↔ observed = Part.some (codec (word, heap))
  rw [Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  constructor
  · rintro ⟨actual, member, equal⟩
    rw [← equal, Equiv.apply_symm_apply]
    exact member
  · intro member
    exact ⟨_, member, codec.symm_apply_apply _⟩

theorem numberedStage_eq_some_iff (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    numberedStage p model initial = Part.some (word, final) ↔
      p.observe model initial = Part.some (encodeResult word final) :=
  decode_eq_some_iff (p.observe model initial) word final

theorem colouredStage_eq_some_iff (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    colouredStage p model initial = Part.some (word, final) ↔
      p.Completes model initial (encodeResult word final) :=
  (decode_eq_some_iff (p.petriObserve model initial) word final).trans
    (p.petriObserve_eq_some_iff model initial (encodeResult word final))

theorem numbered_eq_local (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val rightCells) Q.args) (e : Embedding model.cells cells)
    (f : Embedding rightCells cells) (disjoint : DisjointImages e f) (initial : Heap cells) :
    numbered first second (embedModel model e) (fun word => CellEmbedding.input f (next word)) initial =
      localObserve e f (numberedStage first model) (fun word => numberedStage second ⟨rightCells, next word⟩) initial :=
  observe_eq_local e f disjoint _ _ _ _ (numberedStage_embed first model e)
    (fun word => numberedStage_embed second ⟨rightCells, next word⟩ f) initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Proofs
