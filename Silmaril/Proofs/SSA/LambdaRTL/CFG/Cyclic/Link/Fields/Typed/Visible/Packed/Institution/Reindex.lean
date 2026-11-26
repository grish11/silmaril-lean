module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Signature.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

open CategoryTheory
open Silmaril.Elgot.ITree
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program (PackedEntry MismatchDirection)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a} {Target : TraceSignature.{0}}

theorem observe_mapped {target : Silmaril.Elgot.ITree.Signature.{0}} (entry : PackedEntry left input)
    (f : signature.traceSignature.toSignature ⟶ target)
    (ambient record : Semantics.Env Atom) :
    entry.observeMapped f ambient record = f.tree id (entry.observe ambient record) :=
  (Semantics.Interaction.region_reindex f signature.primitive _ _).symm

theorem observe_reindexed (entry : PackedEntry left input) (f : signature.traceSignature ⟶ Target)
    (ambient record : Semantics.Env Atom) :
    entry.observeReindexed f ambient record = f.hom.tree id (entry.observe ambient record) :=
  observe_mapped entry f.hom ambient record

theorem refinementSentence_reindexed
    {c : Nat} {rightInputs : Fin c → PacketType} {right : Program signature rightInputs outputs}
    {rightInput : Fin c} (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right rightInput)
    (f : signature.traceSignature ⟶ Target) (direction : MismatchDirection)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord).translate f =
      leftEntry.refinementSentenceReindexed rightEntry f direction leftAmbient rightAmbient leftRecord rightRecord := by
  cases direction <;>
    simp only [PackedEntry.refinementSentence, PackedEntry.refinementSentenceReindexed, observe_reindexed] <;>
    exact TraceInstitution.translate_hasTrace f _ _

theorem mutual_valid_reindexed
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (f : signature.traceSignature ⟶ Target)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    (∀ policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature,
      TraceInstitution.Sat policy (leftEntry.refinementSentenceReindexed rightEntry f .leftToRight
        leftAmbient rightAmbient leftRecord rightRecord) ∧
      TraceInstitution.Sat policy (leftEntry.refinementSentenceReindexed rightEntry f .rightToLeft
        leftAmbient rightAmbient leftRecord rightRecord)) ↔
    (∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
      TraceInstitution.Sat policy (leftEntry.refinementSentence rightEntry .leftToRight
        leftAmbient rightAmbient leftRecord rightRecord) ∧
      TraceInstitution.Sat policy (leftEntry.refinementSentence rightEntry .rightToLeft
        leftAmbient rightAmbient leftRecord rightRecord)) := by
  rw [← leftEntry.observe_eq_iff_mutual_valid rightEntry]
  simp only [PackedEntry.refinementSentenceReindexed, forall_and, TraceInstitution.valid_hasTrace_iff,
    observe_reindexed, eq_iff_traceLE]
  exact and_congr f.traceLE_iff f.traceLE_iff

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution
