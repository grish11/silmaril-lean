module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback (packetValue)
open Silmaril.SSA.LambdaRTL (CFG Val upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (Tree)
open Silmaril.Elgot.ITree.Finite (Event)

variable {V : Type 1} {n : Nat} {term : Val (Fin n)} {ty : PacketType}
  (typing : StructuralSeed term ty) (names : Fin n → V)

private theorem eval_iff (initial : V → Value Atom) (packet : Denote ty) :
    packetValue (StructuralSeed.captureEnv names initial) term = PacketType.encode ty packet ↔
      ∀ claim ∈ typing.assignment names packet, initial claim.1 = claim.2 := by
  induction typing with
  | var slot packetType =>
    simp [packetValue, StructuralSeed.captureEnv, StructuralSeed.assignment, slot.isLt]
  | unit => simp [packetValue, PacketType.encode, StructuralSeed.assignment]
  | pair left right ihLeft ihRight =>
    obtain ⟨a, b⟩ := packet
    simp only [packetValue, PacketType.encode, Value.pair.injEq, StructuralSeed.assignment, List.forall_mem_append]
    exact and_congr (ihLeft a) (ihRight b)

private theorem eval_congr {initial other : V → Value Atom}
    (agree : ∀ field ∈ typing.footprint names, initial field.1 = other field.1) :
    packetValue (StructuralSeed.captureEnv names initial) term =
      packetValue (StructuralSeed.captureEnv names other) term := by
  induction typing with
  | var slot packetType =>
    simpa only [packetValue, StructuralSeed.captureEnv, dite_eq_left slot.isLt] using
      agree (names slot, packetType) (by simp [StructuralSeed.footprint])
  | unit => rfl
  | pair left right ihLeft ihRight =>
    exact congrArg₂ Value.pair
      (ihLeft fun field mem => agree field (List.mem_append_left _ mem))
      (ihRight fun field mem => agree field (List.mem_append_right _ mem))

private theorem assignment_names (packet : Denote ty) :
    (typing.assignment names packet).map Prod.fst = (typing.footprint names).map Prod.fst := by
  induction typing with
  | var => rfl
  | unit => rfl
  | pair left right ihLeft ihRight =>
    obtain ⟨a, b⟩ := packet
    simp [StructuralSeed.assignment, StructuralSeed.footprint, ihLeft a, ihRight b]

private theorem assignmentStore_agrees [DecidableEq V]
    (assignment : List (V × Value Atom)) (original : V → Value Atom)
    (holds : ∀ claim ∈ assignment, original claim.1 = claim.2) (name : V)
    (mem : name ∈ assignment.map Prod.fst) :
    StructuralSeed.assignmentStore assignment name = original name := by
  induction assignment with
  | nil => simp at mem
  | cons head tail ih =>
    obtain ⟨register, value⟩ := head
    by_cases same : name = register
    · subst name
      simpa [StructuralSeed.assignmentStore, upd] using (holds (register, value) (by simp)).symm
    · have inTail : name ∈ tail.map Prod.fst := by simpa [same] using mem
      simp only [StructuralSeed.assignmentStore, upd, same, ite_false]
      exact ih (fun claim found => holds claim (List.mem_cons_of_mem _ found)) inTail

variable {K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

theorem evalSeed_congr {initial other : V → Value Atom}
    (agree : ∀ field ∈ left.footprint, initial field.1 = other field.1) :
    left.evalSeed initial = left.evalSeed other :=
  eval_congr left.typedSeed _ agree

theorem observe_eq (initial : V → Value Atom) (packet : Denote inputType) (ambient : Env Atom)
    (checked : left.evalSeed initial = PacketType.encode inputType packet) :
    left.entry.observe ambient (packetRecord packet) =
      observeRaw signature.primitive exits fields source initial :=
  observe_eq_of_provenance left.entry (fun i => left.names[i.val]) left.closed left.accepted left.provenance
    initial packet ambient _ (fun i => by simp [StructuralSeed.captureEnv, i.isLt]) checked

theorem observe_congr {initial other : V → Value Atom}
    (agree : ∀ field ∈ left.footprint, initial field.1 = other field.1)
    (typed : ∃ packet, left.evalSeed initial = PacketType.encode inputType packet) :
    observeRaw signature.primitive exits fields source initial =
      observeRaw signature.primitive exits fields source other := by
  obtain ⟨packet, checked⟩ := typed
  exact (observe_eq left initial packet (fun _ => .unit) checked).symm.trans
    (observe_eq left other packet (fun _ => .unit) ((evalSeed_congr left agree).symm.trans checked))

theorem jointStores_typed {initial : V → Value Atom} (member : initial ∈ left.jointStores right) :
    (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
      (∃ b, right.evalSeed initial = PacketType.encode rightType b) := by
  obtain ⟨assignment, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨⟨a, b⟩, _, found⟩ := List.mem_filterMap.mp present
  dsimp only at found
  split at found
  · rename_i consistent
    cases Option.some.inj found
    have agrees (claim : V × Value Atom) (mem : claim ∈ left.assignment a ++ right.assignment b) :
        StructuralSeed.assignmentStore (left.assignment a ++ right.assignment b) claim.1 = claim.2 :=
      of_decide_eq_true ((List.all_eq_true.mp consistent) claim mem)
    exact ⟨⟨a, (eval_iff left.typedSeed _ _ a).mpr fun claim mem => agrees claim (List.mem_append_left _ mem)⟩,
      ⟨b, (eval_iff right.typedSeed _ _ b).mpr fun claim mem => agrees claim (List.mem_append_right _ mem)⟩⟩
  · contradiction

theorem jointStores_cover (original : V → Value Atom)
    (leftTyped : ∃ a, left.evalSeed original = PacketType.encode inputType a)
    (rightTyped : ∃ b, right.evalSeed original = PacketType.encode rightType b) :
    ∃ initial ∈ left.jointStores right,
      ∀ field ∈ left.footprint ++ right.footprint, initial field.1 = original field.1 := by
  obtain ⟨a, leftChecked⟩ := leftTyped
  obtain ⟨b, rightChecked⟩ := rightTyped
  let assignment := left.assignment a ++ right.assignment b
  have holds : ∀ claim ∈ assignment, original claim.1 = claim.2 := by
    intro claim mem
    rcases List.mem_append.mp mem with fromLeft | fromRight
    · exact (eval_iff left.typedSeed _ original a).mp leftChecked claim fromLeft
    · exact (eval_iff right.typedSeed _ original b).mp rightChecked claim fromRight
  have names : assignment.map Prod.fst = (left.footprint ++ right.footprint).map Prod.fst := by
    simp only [assignment, List.map_append, StructuralEntry.assignment, StructuralEntry.footprint, assignment_names]
  have consistent : assignment.all (fun (name, value) =>
      decide (StructuralSeed.assignmentStore assignment name = value)) = true := by
    apply List.all_eq_true.mpr
    intro claim mem
    exact decide_eq_true ((assignmentStore_agrees assignment original holds _ (List.mem_map_of_mem mem)).trans
      (holds claim mem))
  refine ⟨StructuralSeed.assignmentStore assignment, List.mem_map.mpr ⟨assignment, ?_, rfl⟩, ?_⟩
  · refine List.mem_filterMap.mpr ⟨(a, b),
      List.mem_product.mpr ⟨PacketType.mem_enumerate _ a, PacketType.mem_enumerate _ b⟩, ?_⟩
    change (if assignment.all (fun (name, value) =>
      decide (StructuralSeed.assignmentStore assignment name = value)) then some assignment else none) = _
    simp [consistent]
  · intro field mem
    exact assignmentStore_agrees assignment original holds _ (names ▸ List.mem_map_of_mem mem)

theorem jointStores_eq_nil :
    left.jointStores right = [] ↔ ¬ ∃ initial,
      (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
        (∃ b, right.evalSeed initial = PacketType.encode rightType b) := by
  refine ⟨?_, fun impossible => List.eq_nil_iff_forall_not_mem.mpr fun initial mem =>
    impossible ⟨initial, jointStores_typed left right mem⟩⟩
  rintro empty ⟨original, wellTyped⟩
  obtain ⟨initial, mem, _⟩ := jointStores_cover left right original wellTyped.1 wellTyped.2
  simp [empty] at mem

theorem jointStores_forall_observe
    (rel : Tree (Event signature.Request signature.Reply) (Nat × Value Atom) →
      Tree (Event signature.Request signature.Reply) (Nat × Value Atom) → Prop) :
    (∀ initial ∈ left.jointStores right,
      rel (observeRaw signature.primitive exits fields source initial)
        (observeRaw signature.primitive exits fields target initial)) ↔
    (∀ initial, (∃ a, left.evalSeed initial = PacketType.encode inputType a) →
      (∃ b, right.evalSeed initial = PacketType.encode rightType b) →
      rel (observeRaw signature.primitive exits fields source initial)
        (observeRaw signature.primitive exits fields target initial)) := by
  constructor
  · intro holds original typedLeft typedRight
    obtain ⟨initial, mem, agree⟩ := jointStores_cover left right original typedLeft typedRight
    have typed := jointStores_typed left right mem
    have sameLeft := observe_congr left (fun field found => agree field (List.mem_append_left _ found)) typed.1
    have sameRight := observe_congr right (fun field found => agree field (List.mem_append_right _ found)) typed.2
    exact (congrArg₂ rel sameLeft sameRight).mp (holds initial mem)
  · intro holds initial mem
    have typed := jointStores_typed left right mem
    exact holds initial typed.1 typed.2

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural
