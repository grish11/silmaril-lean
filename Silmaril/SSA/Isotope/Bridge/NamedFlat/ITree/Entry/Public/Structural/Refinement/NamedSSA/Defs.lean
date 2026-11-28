module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison.Thms

/-! # Actual named SSA endpoints of a structural capture comparison -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Elgot.ITree (HasTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}

/-- Version the original written RTL with its selected live-out reads
attached. The existing certificate checks lexical SSA scope at entry
and at every block. -/
def StructuralEntry.versioned
    (_entry : StructuralEntry signature source exits fields inputType outputs) :
    Comparison.LexicalGraph V K F :=
  Comparison.version (CFG.Cyclic.LiveOut.attach fields source)

/-- Run those lexical rows from the version-zero source store. The result
numbers the original exit and retains its payload and selected live-outs. -/
noncomputable def StructuralEntry.observeVersioned
    (entry : StructuralEntry signature source exits fields inputType outputs)
    (initial : V → Value Atom) :=
  Comparison.ssaObserve ⟨treeModel signature.primitive, ⟨fun _ _ => rfl⟩⟩ entry.versioned initial >>=
    fun out => pure (FiniteCFG.packedTreeOutput (treeExitNumber exits out))

/-- The same handled-trace sentence, interpreted on the actual named SSA
translations of both source tables. -/
noncomputable def StructuralEntry.versionedRefinementSentence
    (left : StructuralEntry signature source exits fields inputType outputs)
    (right : StructuralEntry signature target exits fields rightType outputs)
    (initial : V → Value Atom) : TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  ⟨_, left.observeVersioned initial, HasTrace (right.observeVersioned initial)⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
