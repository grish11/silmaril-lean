module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {source : CFG V K P.Instr}
  [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

theorem packed_tree (M : Model (κ := κ) Events P.Instr) (admission : Admission P I fields source)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) admission.program.code =
      LiveOut.observe M I fields source x := by
  calc
    _ = admission.versioned.observe M x := (SSA.observe_tree M admission.versioned x ambient).symm
    _ = _ := ?_
  let m := treeModel M.raw
  let input := store I.version.names I.context x
  have original : (fun reg => input (reg, 0)) = store I.names I.context x :=
    funext (store_version_zero I.names I.context x)
  have run := CFG.Cyclic.Versioning.runPacketLocal_commutes m ⟨fun _ _ => rfl⟩
    (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source) admission.closed input
  rw [original] at run
  change (CFG.Cyclic.runSSA m admission.versioned.source input >>= fun out =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber I.exits out))) = _
  rw [admission.compiled, ← run]
  rw [CFG.Cyclic.LiveOut.run_project]
  simp only [LiveOut.observe, LiveOut.observeRaw, bind_map_left]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
