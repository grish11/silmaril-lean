module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.CaptureDemand.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

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

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "ports" => numberedInterface context exits external

variable (a) in
/-- The empty layout installed by the opt-in path is the inferred least
layout at each row of every certified packet-local table. -/
theorem least_layout (entry : List (Fin n))
    (i : Fin (attached).blocks.length) :
    CaptureDemand.ordered attached (fun j : Fin n => (⟨j.val⟩ : Register)) entry i = [] := by
  simp [CaptureDemand.ordered, CaptureDemand.infer_empty_of_packetClosed attached _ a.closed]

variable [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType context.toList
local notation "C" => AtomValues.carrier (κ := κ)

/-- The actual opt-in packed program computes the named runner's ordered
exit observation at the same caller record. -/
theorem Admission.packed_tree (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) admission.program.code =
      LiveOut.observe M ports fields a.source x :=
  LiveOut.PacketLocal.Admission.packed_tree M ⟨a.closed, admission.versioned, admission.compiled⟩ x ambient

/-- Compare the original typed program with the actual opt-in reversion at
the shared entry and ordered exit interface. -/
theorem Admission.packed_roundTrip (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    {R : Fin blocks → Ty κ}
    (typed : code.HasType context R (LiveOut.exitInterface ports fields).external)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) admission.program.code :=
  (a.packed_observe M typed x ambient).trans (admission.packed_tree M x ambient).symm

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
