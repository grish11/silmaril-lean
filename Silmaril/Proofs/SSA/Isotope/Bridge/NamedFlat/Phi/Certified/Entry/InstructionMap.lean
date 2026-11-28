module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.InstructionMap.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.InstructionMap.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Record (Input)

universe u v
variable {κ V K : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n} {I : Captures V β}
  {D : Fin 1 → Ty κ} [DecidableEq V] [DecidableEq K]
  {P Q : FlatInstitution.Signature.{u, v} κ}

theorem toSSA_ofSSA (source : Phi.Graph V K P.Instr) (inputs : List V)
    (wf : Phi.GlobalSSA.WellFormed source inputs)
    (table : NamedFlat.Entry.SSA P (I.named K D).version)
    (lowered : table.source = Versioning.compile (Phi.lower source)) :
    (Admitted.ofSSA source inputs wf table lowered).toSSA = table := by
  rcases table with ⟨lexical, ⟨blocks, profile, code, typed⟩, count, accepted⟩
  dsimp only at lowered count accepted
  subst lexical
  subst blocks
  rfl

variable [AtomValues κ] {Events : Type u → Type u}

theorem named_observe_map (a : Admitted P I K D) (g : P ⟶ Q)
    (M : Model (κ := κ) Events Q.Instr) (record : Input β) :
    (a.toSSA.map g).observe M record = a.toSSA.observe (FlatInstitution.reduct Events g M) record := by
  unfold NamedFlat.Entry.SSA.observe
  change (CFG.Cyclic.runSSA (NamedFlat.treeModel M.raw) (a.toSSA.source.mapOp g.toSignatureMap.instr) _
    >>= _) = _
  rw [CFG.Cyclic.runSSA_mapOp]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
