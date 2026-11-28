module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (Region)
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

/-- The actual packet-local reversion computes the original named run's
ordered exit and selected live-outs at the same typed caller record. -/
theorem Admission.packed_tree (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) a.program.code =
      LiveOut.observe M I fields source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.packed_tree M a x ambient

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
