module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open CategoryTheory
open Silmaril.Elgot.ITree (TraceSignature)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a} {Target : TraceSignature.{0}}

/-- Reindexing commutes with execution of the actual packed region. -/
theorem PackedEntry.observe_mapped {target : Silmaril.Elgot.ITree.Signature.{0}} (entry : PackedEntry left input)
    (f : signature.traceSignature.toSignature ⟶ target) (ambient record : Semantics.Env Atom) :
    entry.observeMapped f ambient record = f.tree id (entry.observe ambient record) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.observe_mapped
    entry f ambient record

theorem PackedEntry.observe_reindexed (entry : PackedEntry left input) (f : signature.traceSignature ⟶ Target)
    (ambient record : Semantics.Env Atom) :
    entry.observeReindexed f ambient record = f.hom.tree id (entry.observe ambient record) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.observe_reindexed
    entry f ambient record

theorem PackedEntry.refinementSentence_reindexed
    {c : Nat} {rightInputs : Fin c → PacketType} {right : Program signature rightInputs outputs}
    {rightInput : Fin c} (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right rightInput)
    (f : signature.traceSignature ⟶ Target) (direction : MismatchDirection)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord).translate f =
      leftEntry.refinementSentenceReindexed rightEntry f direction leftAmbient rightAmbient leftRecord rightRecord :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.refinementSentence_reindexed
    leftEntry rightEntry f direction leftAmbient rightAmbient leftRecord rightRecord

/-- The existing institutional satisfaction square for the two checked
packed entries and the same supplied records. -/
theorem PackedEntry.sat_reindexed_iff
    {c : Nat} {rightInputs : Fin c → PacketType} {right : Program signature rightInputs outputs}
    {rightInput : Fin c} (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right rightInput)
    (f : signature.traceSignature ⟶ Target) (policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.Sat policy
      (leftEntry.refinementSentenceReindexed rightEntry f direction leftAmbient rightAmbient leftRecord rightRecord) ↔
    TraceInstitution.Sat (policy.reduct f.hom)
      (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord) := by
  rw [← leftEntry.refinementSentence_reindexed rightEntry f]
  exact TraceInstitution.satisfaction f policy _

/-- Injectivity on complete keys and invertibility on typed replies make
universal mutual validity invariant under this signature change. -/
theorem PackedEntry.mutual_valid_reindexed
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
        leftAmbient rightAmbient leftRecord rightRecord)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.mutual_valid_reindexed
    leftEntry rightEntry f leftAmbient rightAmbient leftRecord rightRecord

/-- The original finite verdict decides the reindexed packed mutual
validity over every checked public entry and exact typed packet. -/
theorem weakEq?_iff_mutual_valid_reindexed [DecidableEq F] (left right : Program signature inputs outputs)
    (f : signature.traceSignature ⟶ Target)
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.weakEq? right = true ↔
      ∀ input packet (policy : Silmaril.Logic.ITree.Model.{0, 0} Target.toSignature),
        TraceInstitution.Sat policy ((leftEntry input).refinementSentenceReindexed (rightEntry input) f .leftToRight
          leftAmbient rightAmbient (leftRecord input packet) (rightRecord input packet)) ∧
        TraceInstitution.Sat policy ((leftEntry input).refinementSentenceReindexed (rightEntry input) f .rightToLeft
          leftAmbient rightAmbient (leftRecord input packet) (rightRecord input packet)) :=
  (left.weakEq?_iff_mutual_valid_traceSat right leftEntry rightEntry leftAmbient rightAmbient
    leftRecord rightRecord leftAgrees rightAgrees).trans <| forall_congr' fun input => forall_congr' fun packet =>
      ((leftEntry input).mutual_valid_reindexed (rightEntry input) f leftAmbient rightAmbient
        (leftRecord input packet) (rightRecord input packet)).symm

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program
