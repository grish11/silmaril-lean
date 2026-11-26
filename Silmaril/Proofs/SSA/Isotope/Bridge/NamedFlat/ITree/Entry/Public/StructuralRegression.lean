module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Thms

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev Name := ULift.{1} Nat
private abbrev bit : PacketType := .coprod .unit .unit
private def signature : PrimitiveSignature Unit := ⟨fun _ => bit, fun _ => bit⟩
private def shared : Name := ⟨4⟩
private def leftRead : Name := ⟨5⟩
private def rightRead : Name := ⟨6⟩
private def liveOut : Name := ⟨9⟩
private def exits : List Name := [⟨22⟩, ⟨11⟩]
private def fields (_ : Name) : List Name := [liveOut]
private def outputs (_ : Fin exits.length) : PacketType := .product .unit (.product bit .unit)

private def graph (first second : Name) : CFG Name Name Unit :=
  ⟨.term (.br ⟨12⟩ (.pair (.var first) (.var second))),
    [(⟨12⟩, ⟨⟨7⟩, .let2 ⟨8⟩ liveOut (.val (.var ⟨7⟩)) (.term (.br ⟨11⟩ .unit))⟩)]⟩

private def build (first second : Name) (firstType : PacketType) :
    Option (StructuralEntry signature (graph first second) exits fields (.product firstType bit) outputs) :=
  constructStructural signature (graph first second) exits fields (.product firstType bit)
    (fun _ => .product firstType bit) outputs

private def left := (build shared leftRead bit).get (by decide)
private def right := (build shared rightRead bit).get (by decide)

private theorem leftFootprint : left.footprint = [(shared, bit), (leftRead, bit)] := by decide
example : right.footprint = [(shared, bit), (rightRead, bit)] := by decide

-- Three independently chosen bits, with one shared register written only
-- when its two occurrences demand the same value.
example : (left.jointStores right).length = 8 := by decide

private def original : Name → Value Atom :=
  upd (upd (upd (fun _ => .unit) shared (.inl .unit)) leftRead (.inr .unit)) rightRead (.inl .unit)

private def leftPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inr ⟨⟩)
private def rightPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inl ⟨⟩)

example : left.entry.observe (fun _ => .unit) (packetRecord (inputType := .product bit bit) leftPacket) =
    LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) original :=
  left.observe_eq original leftPacket (fun _ => .unit) (by decide)

example : ∃ initial ∈ left.jointStores right,
    ∀ field ∈ left.footprint ++ right.footprint, initial field.1 = original field.1 :=
  left.jointStores_cover right original ⟨leftPacket, by decide⟩ ⟨rightPacket, by decide⟩

private def changedLiveOut : Name → Value Atom := upd original liveOut (.pair .unit .unit)

example : LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) original =
    LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) changedLiveOut := by
  apply left.observe_eq_of_capture_agree _ ⟨leftPacket, by decide⟩
  intro field mem
  simp only [leftFootprint, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> decide

-- Repeating a name with disjoint raw encodings empties the domain.
private def conflicting := (build shared shared .unit).get (by decide)
example : (conflicting.jointAssignments right).isEmpty = true := by decide

-- Unequal types with a common encoding still admit exactly the compatible stores.
private def overlapping := (build shared shared (.coprod .unit .empty)).get (by decide)
example : (overlapping.jointStores right).length = 2 := by decide

-- Existing named elaboration can express an injection as an instruction,
-- but the structural public readback takes the operand of a direct jump.
example :
    (constructStructural signature
      {graph shared leftRead with
        entry := .let1 ⟨8⟩ (.inl .unit) (.term (.br ⟨12⟩ (.pair (.var ⟨8⟩) (.var leftRead))))}
      exits fields (.product bit bit) (fun _ => .product bit bit) outputs).isNone = true := by decide

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
