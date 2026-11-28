module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Compilation.Thms
public import Silmaril.Logic.Institution.Morphism

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.Elgot.ITree (TraceSignature HasTrace)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

/-- A finite packet primitive signature with its opcode carrier. -/
structure OpcodeSignature where
  Opcode : Type
  primitive : PrimitiveSignature Opcode

namespace OpcodeSignature

/-- Along an admissible arrow, the opcode map preserves exact argument and
reply types and the event map agrees with raw primitive execution. -/
structure Arrow (S T : OpcodeSignature) where
  rename : S.primitive.Renaming T.primitive
  events : S.primitive.traceSignature ⟶ T.primitive.traceSignature
  agrees : ∀ op raw, T.primitive.primitive (rename.opcode op) raw =
    events.hom.tree id (S.primitive.primitive op raw)

variable {S T U : OpcodeSignature}

def Arrow.id (S : OpcodeSignature) : Arrow S S :=
  ⟨⟨_root_.id, fun _ => rfl, fun _ => rfl⟩, 𝟙 _, fun op raw =>
    (Silmaril.Elgot.ITree.Signature.Hom.tree_id (S.primitive.primitive op raw)).symm⟩

def Arrow.comp (f : Arrow S T) (g : Arrow T U) : Arrow S U :=
  ⟨⟨g.rename.opcode ∘ f.rename.opcode,
      fun op => (g.rename.argument (f.rename.opcode op)).trans (f.rename.argument op),
      fun op => (g.rename.reply (f.rename.opcode op)).trans (f.rename.reply op)⟩,
    f.events ≫ g.events,
    by
      intro op raw
      change U.primitive.primitive (g.rename.opcode (f.rename.opcode op)) raw = _
      rw [g.agrees, f.agrees]
      exact (Silmaril.Elgot.ITree.Signature.Hom.tree_comp f.events.hom g.events.hom _root_.id _root_.id
        (S.primitive.primitive op raw)).symm⟩

end OpcodeSignature

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]

/-- Keep the two written mutable endpoints and the exact common initial
store. The ordered exits and selected live-outs are fixed by the institution. -/
structure Endpoints (V K : Type 1) (S : OpcodeSignature) where
  left : CFG V K S.Opcode
  right : CFG V K S.Opcode
  initial : V → Value Atom

variable {S T : OpcodeSignature} {exits : List K} {fields : K → List V}

def Endpoints.map (point : Endpoints V K S) (f : OpcodeSignature.Arrow S T) : Endpoints V K T :=
  ⟨point.left.mapOp f.rename.opcode, point.right.mapOp f.rename.opcode, point.initial⟩

/-- Checked admission includes the public occurrence gate and both independent
decodes from the original store. The seed types need not coincide. -/
structure Admission (point : Endpoints V K S) (exits : List K) (fields : K → List V) where
  leftType : PacketType
  rightType : PacketType
  outputs : Fin exits.length → PacketType
  left : StructuralEntry S.primitive point.left exits fields leftType outputs
  right : StructuralEntry S.primitive point.right exits fields rightType outputs
  checked : (left.checkOccurrenceComparison? right).isSome = true
  leftPacket : Denote leftType
  rightPacket : Denote rightType
  leftSeed : left.seed? point.initial = some leftPacket
  rightSeed : right.seed? point.initial = some rightPacket

def Admission.comparison {point : Endpoints V K S} (a : Admission point exits fields) :
    OccurrenceComparison a.left a.right :=
  (a.left.checkOccurrenceComparison? a.right).get a.checked

def Admission.map {point : Endpoints V K S} (a : Admission point exits fields) (f : OpcodeSignature.Arrow S T) :
    Admission (point.map f) exits fields :=
  ⟨a.leftType, a.rightType, a.outputs, a.left.mapOpcode f.rename, a.right.mapOpcode f.rename,
    (a.left.checkOccurrenceComparison?_isSome_mapOpcode a.right f.rename).trans a.checked,
    a.leftPacket, a.rightPacket,
    (a.left.seed?_mapOpcode f.rename point.initial).trans a.leftSeed,
    (a.right.seed?_mapOpcode f.rename point.initial).trans a.rightSeed⟩

/-- A source sentence keeps the written endpoints. Successful admission
is a property of the sentence, independent of its choice of certificate. -/
def Sentence (S : OpcodeSignature) (exits : List K) (fields : K → List V) :=
  { point : Endpoints V K S // Nonempty (Admission point exits fields) }

def Sentence.map (φ : Sentence S exits fields) (f : OpcodeSignature.Arrow S T) : Sentence T exits fields :=
  ⟨φ.val.map f, φ.property.elim fun a => ⟨a.map f⟩⟩

/-- Original mutable satisfaction at the selected store and ordered exits. -/
noncomputable def Endpoints.observe (point : Endpoints V K S) (exits : List K) (fields : K → List V) :
    TraceInstitution.Sentence.{0, 1} S.primitive.traceSignature :=
  ⟨_, LiveOut.observeRaw S.primitive.primitive exits fields point.left point.initial,
    HasTrace (LiveOut.observeRaw S.primitive.primitive exits fields point.right point.initial)⟩

/-- The actual admitted occurrence comparison, using its two decoded packets. -/
noncomputable def Admission.observe {point : Endpoints V K S} (a : Admission point exits fields) :
    TraceInstitution.Sentence.{0, 1} S.primitive.traceSignature :=
  a.comparison.sentence a.leftPacket a.rightPacket

/-- Translate through any successful admission. The observation equation
ensures that this choice has no effect on the translated sentence. -/
noncomputable def Sentence.compile (φ : Sentence S exits fields) :
    TraceInstitution.Sentence.{0, 1} S.primitive.traceSignature :=
  (Classical.choice φ.property).observe

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
