module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Proofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CarriedAddress.Institution.RuntimeEntry (decodePayload encode_decodePayload)

variable {P Q : EntrySignature} {cells : Nat} {args : List ValueSort}

set_option backward.isDefEq.respectTransparency false

private theorem stage_returns (graph : Graph args) (input : Tuple (Val cells) args)
    (initial final : Heap cells) (word : Word) :
    (Petri.lower graph).Returns (thetaRuntime cells) (encodeInput initial input) (encodeResult word final) ↔
      graph.Returns input initial word final :=
  (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).symm.trans (Petri.lower_finishes_iff graph input initial word final)

private theorem returns_split (p : Program P) (model : EntryModel P) (initial final : Heap model.cells)
    (firstWord secondWord thirdWord : Word) :
    p.numberedReturns model initial (firstWord, secondWord, thirdWord, final) ↔
      ∃ middle, p.pair.nativeReturns model initial (firstWord, secondWord, middle) ∧
        p.third.Returns (p.wiring.select secondWord (p.pair.wiring.select firstWord model.input))
          middle thirdWord final := by
  unfold Program.numberedReturns Program.emitNumbered Triple.program
  rw [Triple.returns_iff_stages (P := P) (Q := p.pair.next) (R := p.last)]
  simp only [stage_returns, Linked.Satisfaction.Program.nativeReturns, nativeReturns]
  constructor
  · rintro ⟨firstHeap, middle, first, second, third⟩
    exact ⟨middle, ⟨firstHeap, first, second⟩, third⟩
  · rintro ⟨middle, ⟨firstHeap, first, second⟩, third⟩
    exact ⟨firstHeap, middle, first, second, third⟩

theorem numbered_returns_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) (out : Triple.Result model.cells) :
    (p.map h).numberedReturns model initial out ↔ p.numberedReturns (reduct h model) initial out := by
  obtain ⟨firstWord, secondWord, thirdWord, final⟩ := out
  rw [returns_split, returns_split]
  apply exists_congr
  intro middle
  refine and_congr (p.pair.native_returns_map h model initial _) ?_
  change p.third.Returns (p.wiring.select secondWord
    ((p.pair.wiring.map (EntrySignature.Hom.port h)).select firstWord model.input)) middle thirdWord final ↔ _
  rw [Boundary.Wiring.select_map]
  rfl

theorem holdsWith_congr (s : Sentence P) (left right : Program P → Returns cells)
    (same : ∀ p initial out, left p initial out ↔ right p initial out) :
    s.HoldsWith left ↔ s.HoldsWith right := by
  cases s <;> simp only [Sentence.HoldsWith, same]

theorem satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.map h).NumberedHolds model ↔ s.NumberedHolds (reduct h model) := by
  cases s <;> (simp only [Sentence.map, Sentence.NumberedHolds, Sentence.HoldsWith, numbered_returns_map]; rfl)

private theorem forall_entry (holds : Tuple (WireVal cells) (carrier P.args) → Prop) :
    (∀ raw, holds raw) ↔ ∀ (input : Tuple (Val cells) P.args) (heap : Heap cells), holds (encodeInput heap input) :=
  ⟨fun all input heap => all (encodeInput heap input), fun all raw =>
    let entry := decodePayload raw
    (encode_decodePayload raw) ▸ all entry.input entry.heap⟩

theorem numbered_eq_some_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Triple.Result model.cells) :
    p.numberedObserve model initial = Part.some (resultCodec model.cells out) ↔
      p.numberedReturns model initial out :=
  RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _

private theorem mem_observe (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Triple.Result model.cells) :
    resultCodec model.cells out ∈ p.numberedObserve model initial ↔ p.numberedReturns model initial out :=
  Part.eq_some_iff.symm.trans (numbered_eq_some_iff p model initial out)

private theorem equation_iff (lhs rhs : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    lhs.numberedObserve model initial = rhs.numberedObserve model initial ↔
      ∀ out, lhs.numberedReturns model initial out ↔ rhs.numberedReturns model initial out := by
  constructor
  · intro equal out
    simp only [← mem_observe, equal]
  · intro returns
    apply Part.ext
    intro raw
    obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
    simpa only [mem_observe] using returns out

private theorem termination_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    (p.numberedObserve model initial).Dom ↔ ∃ out, p.numberedReturns model initial out := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨raw, returned⟩
    obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
    exact ⟨out, (mem_observe p model initial out).mp returned⟩
  · rintro ⟨out, returned⟩
    exact ⟨_, (mem_observe p model initial out).mpr returned⟩

theorem room_satisfaction (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) s.numbered ↔
      ∀ input : Tuple (Val cells) P.args, s.NumberedHolds ⟨cells, input⟩ := by
  cases s with
  | equation lhs rhs =>
    change (∀ raw, RuntimeObservation.observe (thetaRuntime cells) lhs.emitNumbered.graph raw =
      RuntimeObservation.observe (thetaRuntime cells) rhs.emitNumbered.graph raw) ↔ _
    exact (forall_entry (P := P) (fun raw => RuntimeObservation.observe (thetaRuntime cells) lhs.emitNumbered.graph raw =
      RuntimeObservation.observe (thetaRuntime cells) rhs.emitNumbered.graph raw)).trans
      (forall_congr' fun input => forall_congr' fun initial => equation_iff lhs rhs ⟨cells, input⟩ initial)
  | terminates p =>
    change (∀ raw, (RuntimeObservation.observe (thetaRuntime cells) p.emitNumbered.graph raw).Dom) ↔ _
    exact (forall_entry (P := P) (fun raw => (RuntimeObservation.observe (thetaRuntime cells)
      p.emitNumbered.graph raw).Dom)).trans
      (forall_congr' fun input => forall_congr' fun initial => termination_iff p ⟨cells, input⟩ initial)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Proofs
