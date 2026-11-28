module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (Tree)
open Silmaril.Elgot.ITree.Finite (Event)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

theorem StructuralEntry.evalSeed_eq_of_capture_agree {initial other : V → Value Atom}
    (agree : ∀ field ∈ left.footprint, initial field.1 = other field.1) :
    left.evalSeed initial = left.evalSeed other :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.evalSeed_congr left agree

/-- Exact row and seed readback relate the actual packed entry to the
original named runner with its ordered exits and selected live-outs. -/
theorem StructuralEntry.observe_eq (initial : V → Value Atom) (packet : Denote inputType) (ambient : Env Atom)
    (checked : left.evalSeed initial = PacketType.encode inputType packet) :
    left.entry.observe ambient (packetRecord packet) =
      LiveOut.observeRaw signature.primitive exits fields source initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.observe_eq left initial packet ambient checked

theorem StructuralEntry.observe_eq_of_capture_agree {initial other : V → Value Atom}
    (agree : ∀ field ∈ left.footprint, initial field.1 = other field.1)
    (typed : ∃ packet, left.evalSeed initial = PacketType.encode inputType packet) :
    LiveOut.observeRaw signature.primitive exits fields source initial =
      LiveOut.observeRaw signature.primitive exits fields source other :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.observe_congr left agree typed

/-- Every enumerated assignment gives both entries a checked typed packet. -/
theorem StructuralEntry.jointStores_typed {initial : V → Value Atom} (member : initial ∈ left.jointStores right) :
    (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
      (∃ b, right.evalSeed initial = PacketType.encode rightType b) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.jointStores_typed left right member

/-- Each common store supplying both seed types has a representative
agreeing on every capture occurrence of both programs. -/
theorem StructuralEntry.jointStores_cover (original : V → Value Atom)
    (leftTyped : ∃ a, left.evalSeed original = PacketType.encode inputType a)
    (rightTyped : ∃ b, right.evalSeed original = PacketType.encode rightType b) :
    ∃ initial ∈ left.jointStores right,
      ∀ field ∈ left.footprint ++ right.footprint, initial field.1 = original field.1 :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.jointStores_cover left right original leftTyped rightTyped

/-- Repeated uses of a name constrain one raw value. Incompatible type
uses produce an empty domain exactly when no common typed store exists. -/
theorem StructuralEntry.jointStores_eq_nil_iff :
    left.jointStores right = [] ↔ ¬ ∃ initial,
      (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
        (∃ b, right.evalSeed initial = PacketType.encode rightType b) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.jointStores_eq_nil left right

/-- A relation on the two original observations holds on the enumerated
representatives exactly when it holds on every common typed store. -/
theorem StructuralEntry.jointStores_forall_observe_iff
    (rel : Tree (Event signature.Request signature.Reply) (Nat × Value Atom) →
      Tree (Event signature.Request signature.Reply) (Nat × Value Atom) → Prop) :
    (∀ initial ∈ left.jointStores right,
      rel (LiveOut.observeRaw signature.primitive exits fields source initial)
        (LiveOut.observeRaw signature.primitive exits fields target initial)) ↔
    (∀ initial, (∃ a, left.evalSeed initial = PacketType.encode inputType a) →
      (∃ b, right.evalSeed initial = PacketType.encode rightType b) →
      rel (LiveOut.observeRaw signature.primitive exits fields source initial)
        (LiveOut.observeRaw signature.primitive exits fields target initial)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.jointStores_forall_observe left right rel

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
