module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Defs

/-! # Directed handled-trace sentences for admitted occurrence entries -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Elgot.ITree (HasTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  {left : StructuralEntry signature source exits fields inputType outputs}
  {right : StructuralEntry signature target exits fields rightType outputs}

/-- The existing handled-trace sentence at two independently typed
occurrence entries. Shared-store comparisons require both decoder equations. -/
noncomputable def OccurrenceAdmission.refinementSentence
    (_leftAdmission : OccurrenceAdmission left) (_rightAdmission : OccurrenceAdmission right)
    (a : Denote inputType) (b : Denote rightType) :
    TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  ⟨_, left.observeOccurrences a, HasTrace (right.observeOccurrences b)⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
