module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Comparison.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.InstructionMap.Thms

/-! # Relabel the evidence of a typed φ admission -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open CategoryTheory
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics.Interaction.Typed.Ordered (FlatInstitution.Signature)

universe u v
variable {κ V K : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n} {I : Captures V β}
  {D : Fin 1 → Ty κ} [DecidableEq V] [DecidableEq K]
  {P Q : FlatInstitution.Signature.{u, v} κ}

/-- Retain an admitted lexical table at the actual lowering of a well-formed
φ graph. The equality identifies the internal profile's block positions. -/
def Admitted.ofSSA (source : Phi.Graph V K P.Instr) (inputs : List V)
    (wf : Phi.GlobalSSA.WellFormed source inputs)
    (table : NamedFlat.Entry.SSA P (I.named K D).version)
    (lowered : table.source = Versioning.compile (Phi.lower source)) : Admitted P I K D :=
  let evidence : Σ profile : Fin (blockCount source) → Ty κ,
      Admission source inputs I.names β profile D := by
    rcases table with ⟨lexical, ⟨blocks, profile, code, typed⟩, count, accepted⟩
    dsimp only at lowered count accepted
    subst lexical
    subst blocks
    exact ⟨profile, ⟨wf, code, (NamedFlat.elaborateAt_eq _ _ _).symm.trans accepted, typed⟩⟩
  ⟨source, inputs, evidence.1, evidence.2⟩

/-- Relabel the admitted source and the existing named certificate at the
same capture, internal block, and return types. -/
def Admitted.map (a : Admitted P I K D) (g : P ⟶ Q) : Admitted Q I K D :=
  let op := g.toSignatureMap.instr
  .ofSSA (a.source.mapOp op) a.inputs (a.admission.wellFormed.mapOp op) (a.toSSA.map g)
    ((congrArg Versioning.compile (Phi.lower_mapOp op a.source)).trans
      (Versioning.compile_mapOp op (Phi.lower a.source))).symm

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
