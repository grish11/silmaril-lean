module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
open Silmaril.SSA.LambdaRTL (CFG)

theorem arrow_ext {S T : OpcodeSignature} {f g : OpcodeSignature.Arrow S T}
    (opcodes : f.rename.opcode = g.rename.opcode) (events : f.events = g.events) : f = g := by
  rcases f with ⟨⟨f, _, _⟩, fe, _⟩
  rcases g with ⟨⟨g, _, _⟩, ge, _⟩
  dsimp only at opcodes events
  subst g
  subst ge
  rfl

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]
  {S T U : OpcodeSignature} {exits : List K} {fields : K → List V}

theorem map_id (φ : Sentence S exits fields) : φ.map (OpcodeSignature.Arrow.id S) = φ := by
  apply Subtype.ext
  change φ.val.map (OpcodeSignature.Arrow.id S) = φ.val
  cases φ.val
  simp only [Endpoints.map, OpcodeSignature.Arrow.id, CFG.mapOp_id]

theorem map_comp (φ : Sentence S exits fields) (f : OpcodeSignature.Arrow S T) (g : OpcodeSignature.Arrow T U) :
    φ.map (f.comp g) = (φ.map f).map g := by
  apply Subtype.ext
  change φ.val.map (f.comp g) = (φ.val.map f).map g
  simp only [Endpoints.map, OpcodeSignature.Arrow.comp, CFG.mapOp_comp]

theorem observe_original {point : Endpoints V K S} (a : Admission point exits fields) :
    a.observe = point.observe exits fields :=
  a.comparison.sentence_eq_original point.initial a.leftPacket a.rightPacket a.leftSeed a.rightSeed

theorem observe_map {point : Endpoints V K S} (a : Admission point exits fields) (f : OpcodeSignature.Arrow S T) :
    (a.map f).observe = a.observe.translate f.events :=
  a.comparison.sentence_mapInstr (a.map f).comparison f.events f.agrees a.leftPacket a.rightPacket
    (a.comparison.leftAdmission.erase_mapOpcode f.rename (a.map f).comparison.leftAdmission)
    (a.comparison.rightAdmission.erase_mapOpcode f.rename (a.map f).comparison.rightAdmission)
    (a.left.occurrenceStore_mapOpcode f.rename a.leftPacket) (a.right.occurrenceStore_mapOpcode f.rename a.rightPacket)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
