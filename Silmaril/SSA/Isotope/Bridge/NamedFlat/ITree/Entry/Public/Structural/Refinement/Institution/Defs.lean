module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory
open Silmaril.Elgot.ITree (HasTrace TraceSignature)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}

/-- The existing handled-trace sentence at one common named store. Each
runner retains the declared ordered exit and its selected live-out fields. -/
noncomputable def StructuralEntry.refinementSentenceAt
    (_left : StructuralEntry signature source exits fields inputType outputs)
    (_right : StructuralEntry signature target exits fields rightType outputs)
    (initial : V → Value Atom) : TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  ⟨_, LiveOut.observeRaw signature.primitive exits fields source initial,
    HasTrace (LiveOut.observeRaw signature.primitive exits fields target initial)⟩

/-- Compare the two actual packed starts in the existing trace institution,
using separate typed seeds and leaving the ordered output profile fixed. -/
noncomputable def StructuralEntry.packedRefinementSentenceReindexed
    (left : StructuralEntry signature source exits fields inputType outputs)
    (right : StructuralEntry signature target exits fields rightType outputs)
    {Target : TraceSignature.{0}} (f : signature.traceSignature ⟶ Target)
    (ambient : Env Atom) (a : Denote inputType) (b : Denote rightType) :
    TraceInstitution.Sentence.{0, 1} Target :=
  left.entry.refinementSentenceReindexed right.entry f .leftToRight ambient ambient
    (packetRecord a) (packetRecord b)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
