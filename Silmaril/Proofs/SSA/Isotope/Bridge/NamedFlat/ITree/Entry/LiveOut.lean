module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {source : CFG V K P.Instr}
  [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

theorem observe_rtl (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (x : Ty.denote C A) : a.rtl.observe M x = observe M I fields source x := by
  change (CFG.Cyclic.run (treeModel M.raw) a.rtl.source (store I.names I.context x) >>= fun out =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber I.exits (obs out)))) = _
  rw [a.attached, CFG.Cyclic.LiveOut.run_project]
  simp only [observe, observeRaw, bind_map_left]

theorem packed_tree (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) a.program.code = observe M I fields source x :=
  (SSA.observe_tree M a.rtl.versioned x ambient).symm.trans
    ((RTL.observe_version M a.rtl x).symm.trans (observe_rtl M a x))

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut
