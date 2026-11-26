module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}
  {a : Lowered (numberedInterface context exits external) fields code}
  [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType context.toList
local notation "C" => AtomValues.carrier (κ := κ)
local notation "ports" => numberedInterface context exits external

theorem packed_tree (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) admission.program.code =
      LiveOut.observe M ports fields a.source x := by
  calc
    _ = admission.versioned.observe M x := (SSA.observe_tree M admission.versioned x ambient).symm
    _ = _ := ?_
  let m := treeModel M.raw
  let input := store (Interface.names (Interface.version ports)) context x
  have original : (fun reg => input (reg, 0)) = store (Interface.names ports) context x :=
    funext (store_version_zero (Interface.names ports) context x)
  have run := CFG.Cyclic.Versioning.runPacketLocal_commutes m ⟨fun _ _ => rfl⟩
    (withLiveOut (P := P) fields a.source) a.closed input
  rw [original] at run
  change (CFG.Cyclic.runSSA m admission.versioned.source input >>= fun out =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber exits out))) = _
  rw [admission.compiled, ← run]
  change ((obs <$> CFG.Cyclic.run m (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst)
    a.source) (store (Interface.names ports) context x)) >>= _) = _
  rw [CFG.Cyclic.LiveOut.run_project]
  simp only [LiveOut.observe, LiveOut.observeRaw, bind_map_left]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
