module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Institution.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut

open CategoryTheory
open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P Q S : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)}

private theorem admitted_ext {a b : Admitted P I fields} (src : a.source = b.source)
    (rtl : a.certificate.rtl = b.certificate.rtl) : a = b := by
  cases a with
  | mk source cert =>
    cases b with
    | mk _ other =>
      cases src
      cases cert
      cases other
      cases rtl
      rfl

theorem admitted_map_id (a : Admitted P I fields) : a.map (𝟙 P) = a :=
  admitted_ext (CFG.mapOp_id a.source) (RTL.map_id a.certificate.rtl)

theorem admitted_map_comp (a : Admitted P I fields) (g : P ⟶ Q) (h : Q ⟶ S) :
    a.map (g ≫ h) = (a.map g).map h :=
  admitted_ext (CFG.mapOp_comp g.toSignatureMap.instr h.toSignatureMap.instr a.source)
    (RTL.map_comp g h a.certificate.rtl)

variable [AtomValues κ] {Events : Type u → Type u}

theorem observe_mapOp (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr)
    (source : CFG V K P.Instr)
    (x : Ty.denote (AtomValues.carrier (κ := κ)) (Region.packedInputType I.context.toList)) :
    observe M I fields (source.mapOp g.toSignatureMap.instr) x =
      observe (FlatInstitution.reduct Events g M) I fields source x := by
  let m := treeModel M.raw
  let opcode := g.toSignatureMap.instr
  let inputs := store I.names I.context x
  let selected := fun k => (fields k).map Prod.fst
  let finish := fun p : CFG.Cyclic.Transfer V K (Value (Sigma (AtomValues.carrier (κ := κ)))) => pure (f := ModelTree Events)
    (FiniteCFG.packedTreeOutput (treeExitNumber I.exits (obs p)))
  have run := CFG.Cyclic.run_mapOp opcode m source inputs
  change (CFG.Cyclic.run m (source.mapOp opcode) inputs >>= fun p =>
      finish (CFG.Cyclic.LiveOut.project m selected p)) =
    (CFG.Cyclic.run (m.reduct opcode) source inputs >>= fun p =>
      finish (CFG.Cyclic.LiveOut.project (m.reduct opcode) selected p))
  rw [run]
  simp only [CFG.Cyclic.LiveOut.project_reduct]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut
