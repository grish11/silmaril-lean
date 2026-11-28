module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Footprint.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public (Seeded packetRecord)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback (packetValue)
open Silmaril.SSA.LambdaRTL (CFG Val upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (HandledTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {leftCapture rightCapture : V} {leftType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : Seeded signature source exits fields leftCapture leftType outputs)
  (right : Seeded signature target exits fields rightCapture rightType outputs)

private theorem packetValue_congr {record other : Env Atom} (seed : Val (Fin 1))
    (agree : ∀ i ∈ seed.fv, record i.val = other i.val) :
    packetValue record seed = packetValue other seed := by
  induction seed with
  | var i => exact agree i (Finset.mem_singleton_self i)
  | unit => rfl
  | pair a b ihA ihB =>
    exact congrArg₂ Value.pair
      (ihA fun i mem => agree i (Finset.mem_union.mpr (.inl mem)))
      (ihB fun i mem => agree i (Finset.mem_union.mpr (.inr mem)))

theorem seed_congr {initial other : V → Value Atom}
    (agree : ∀ v ∈ left.initialCaptures, initial v = other v) :
    left.seed? initial = left.seed? other := by
  have seed : left.evalSeed initial = left.evalSeed other :=
    packetValue_congr left.provenance.seed fun i mem => agree leftCapture (Finset.mem_image.mpr ⟨i, mem, rfl⟩)
  simp only [Seeded.seed?, seed]

theorem observe_congr {initial other : V → Value Atom}
    (agree : ∀ v ∈ left.initialCaptures, initial v = other v)
    (typed : (left.seed? initial).isSome = true) :
    observeRaw signature.primitive exits fields source initial =
      observeRaw signature.primitive exits fields source other := by
  obtain ⟨packet, checked⟩ := Option.isSome_iff_exists.mp typed
  have matching := (seed_congr left agree).symm.trans checked
  exact (left.observe_eq initial packet (fun _ => .unit) ((left.seed?_eq_some_iff _ _).mp checked)).symm.trans
    (left.observe_eq other packet (fun _ => .unit) ((left.seed?_eq_some_iff _ _).mp matching))

private theorem installCapture_eq (supported : left.LiteralOrClosed)
    {original : V → Value Atom} {packet : Denote leftType} (checked : left.seed? original = some packet)
    (initial : V → Value Atom) (v : V) :
    left.installCapture packet initial v = if v ∈ left.initialCaptures then original v else initial v := by
  rcases supported with literal | closed
  · have captures : left.initialCaptures = {leftCapture} := by
      simp [Seeded.initialCaptures, literal, Val.fv]
    have enc : original leftCapture = PacketType.encode leftType packet := by
      have eq := of_decide_eq_true ((left.seed?_eq_some_iff _ _).mp checked)
      simpa only [Seeded.evalSeed, literal, packetValue, packetRecord] using eq
    by_cases same : v = leftCapture
    · subst v
      simp [Seeded.installCapture, captures, upd, enc]
    · simp [Seeded.installCapture, captures, upd, same]
  · simp [Seeded.installCapture, Seeded.initialCaptures, closed]

private theorem members_typed {initial : V → Value Atom} (mem : initial ∈ left.footprintStores right) :
    (left.seed? initial).isSome = true ∧ (right.seed? initial).isSome = true := by
  obtain ⟨⟨leftPacket, rightPacket⟩, _, found⟩ := List.mem_filterMap.mp mem
  dsimp only at found
  split at found
  · rename_i checked
    rw [Bool.and_eq_true] at checked
    obtain ⟨leftChecked, rightChecked⟩ := checked
    cases Option.some.inj found
    exact ⟨Option.isSome_iff_exists.mpr ⟨_, (left.seed?_eq_some_iff _ _).mpr leftChecked⟩,
      Option.isSome_iff_exists.mpr ⟨_, (right.seed?_eq_some_iff _ _).mpr rightChecked⟩⟩
  · contradiction

theorem covers (leftSupported : left.LiteralOrClosed) (rightSupported : right.LiteralOrClosed)
    (original : V → Value Atom) (typedLeft : (left.seed? original).isSome = true)
    (typedRight : (right.seed? original).isSome = true) :
    ∃ initial ∈ left.footprintStores right,
      ∀ v ∈ left.initialCaptures ∪ right.initialCaptures, initial v = original v := by
  obtain ⟨leftPacket, leftSeed⟩ := Option.isSome_iff_exists.mp typedLeft
  obtain ⟨rightPacket, rightSeed⟩ := Option.isSome_iff_exists.mp typedRight
  let initial := right.installCapture rightPacket (left.installCapture leftPacket (fun _ => .unit))
  have agree : ∀ v ∈ left.initialCaptures ∪ right.initialCaptures, initial v = original v := by
    intro v mem
    dsimp only [initial]
    rw [installCapture_eq right rightSupported rightSeed, installCapture_eq left leftSupported leftSeed]
    rcases Finset.mem_union.mp mem with inLeft | inRight
    · simp [inLeft]
    · simp [inRight]
  have leftChecked := (left.seed?_eq_some_iff initial leftPacket).mp <|
    (seed_congr left (fun v mem => agree v (Finset.mem_union.mpr (.inl mem)))).trans leftSeed
  have rightChecked := (right.seed?_eq_some_iff initial rightPacket).mp <|
    (seed_congr right (fun v mem => agree v (Finset.mem_union.mpr (.inr mem)))).trans rightSeed
  refine ⟨initial, List.mem_filterMap.mpr ⟨(leftPacket, rightPacket), List.mem_product.mpr
    ⟨PacketType.mem_enumerate _ _, PacketType.mem_enumerate _ _⟩, ?_⟩, agree⟩
  change (if left.checkSeed initial leftPacket && right.checkSeed initial rightPacket then some initial else none) = _
  simp [leftChecked, rightChecked]

private abbrev RefinesAt (signature : PrimitiveSignature F) (source target : CFG V K F)
    (exits : List K) (fields : K → List V) (initial : V → Value Atom) : Prop :=
  ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
    ∀ x, policy.initial x → ∀ trace,
      HandledTrace policy.step x (observeRaw signature.primitive exits fields source initial) trace →
      HandledTrace policy.step x (observeRaw signature.primitive exits fields target initial) trace

private theorem representatives_iff (leftSupported : left.LiteralOrClosed) (rightSupported : right.LiteralOrClosed) :
    (∀ i : Fin (left.footprintStores right).length,
      RefinesAt signature source target exits fields (left.footprintStores right)[i.val]) ↔
      ∀ initial, (left.seed? initial).isSome = true → (right.seed? initial).isSome = true →
        RefinesAt signature source target exits fields initial := by
  constructor
  · intro holds original typedLeft typedRight
    obtain ⟨initial, mem, agree⟩ := covers left right leftSupported rightSupported original typedLeft typedRight
    obtain ⟨i, hi, atIndex⟩ := List.getElem_of_mem mem
    have wellTyped := members_typed left right mem
    have sameLeft := observe_congr left (fun v hv => agree v (Finset.mem_union.mpr (.inl hv))) wellTyped.1
    have sameRight := observe_congr right (fun v hv => agree v (Finset.mem_union.mpr (.inr hv))) wellTyped.2
    have atStore : RefinesAt signature source target exits fields initial := atIndex ▸ holds ⟨i, hi⟩
    intro policy x started trace seen
    let sees := fun tree => HandledTrace policy.step x tree trace
    exact (congrArg sees sameRight).mp (atStore policy x started trace ((congrArg sees sameLeft).mpr seen))
  · intro holds i
    have typed := members_typed left right (List.getElem_mem (l := left.footprintStores right) i.isLt)
    exact holds _ typed.1 typed.2

theorem eq_some [DecidableEq F] (verdict : Bool) :
    left.refinementOverCaptures? right = some verdict ↔
      left.LiteralOrClosed ∧ right.LiteralOrClosed ∧
      (verdict = true ↔
        ∀ initial, (left.seed? initial).isSome = true → (right.seed? initial).isSome = true →
          ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
            ∀ x, policy.initial x → ∀ trace,
              HandledTrace policy.step x (observeRaw signature.primitive exits fields source initial) trace →
              HandledTrace policy.step x (observeRaw signature.primitive exits fields target initial) trace) := by
  by_cases supported : left.LiteralOrClosed ∧ right.LiteralOrClosed
  · have typed (i : Fin (left.footprintStores right).length) :=
      members_typed left right (List.getElem_mem (l := left.footprintStores right) i.isLt)
    rw [Seeded.refinementOverCaptures?, ite_eq_left supported, Seeded.refinementOverStores?_eq_some_iff]
    have cover := representatives_iff left right supported.1 supported.2
    exact ⟨fun h => ⟨supported.1, supported.2, h.2.trans cover⟩, fun h => ⟨typed, h.2.2.trans cover.symm⟩⟩
  · rw [Seeded.refinementOverCaptures?, ite_eq_right supported]
    simp only [reduceCtorEq, false_iff]
    exact fun h => supported ⟨h.1, h.2.1⟩

theorem eq_none [DecidableEq F] :
    left.refinementOverCaptures? right = none ↔ ¬ (left.LiteralOrClosed ∧ right.LiteralOrClosed) := by
  by_cases supported : left.LiteralOrClosed ∧ right.LiteralOrClosed
  · rw [Seeded.refinementOverCaptures?, ite_eq_left supported, Seeded.refinementOverStores?_eq_none_iff]
    refine ⟨?_, fun rejected => (rejected supported).elim⟩
    rintro ⟨i, bad⟩ _
    have typed := members_typed left right (List.getElem_mem (l := left.footprintStores right) i.isLt)
    rcases bad with bad | bad
    · simpa [bad] using typed.1
    · simpa [bad] using typed.2
  · rw [Seeded.refinementOverCaptures?, ite_eq_right supported]
    exact ⟨fun _ => supported, fun _ => rfl⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint
