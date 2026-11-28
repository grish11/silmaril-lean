module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile

/-! # The exact capture profile and remaining admission conditions -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v w

/-- A row read back with only its packet parameter in scope is packet-closed. -/
theorem block_packetClosed {V K : Type w} {F : Type v} [DecidableEq V] {n labels : Nat}
    {index : K → Option (Fin labels)} (block : CFG.Block V K F) {flat : LambdaSSA.Flat F labels (n + 1)}
    (read : body index (blockNames block.param) block.body = some flat) :
    block.body.toRegion.fv ⊆ {block.param} :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.block_packetClosed block read

/-- Successful scoped readback already certifies packet closure, since
each block is elaborated with only its packet parameter in scope. -/
theorem elaborateAt_packetClosed {V K : Type w} {F : Type v}
    [DecidableEq V] [DecidableEq K] {n blocks : Nat} (graph : CFG V K F) (exits : List K)
    (names : Fin n → V) (count : graph.blocks.length = blocks)
    {code : FiniteCFG F blocks exits.length n}
    (readback : elaborateAt graph exits names blocks count = some code) :
    CFG.Cyclic.RoundTrip.PacketClosed graph :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.elaborateAt_packetClosed graph exits names count readback

/-- The numbered inputs lie below the packet register. All local depths
give distinct registers strictly above the packet register. -/
theorem freshRegisters_bounds (n : Nat) :
    (freshRegisters.{u} n).parameter.down = n ∧
      Function.Injective (freshRegisters.{u} n).localAt ∧
      ∀ depth, n < ((freshRegisters.{u} n).localAt depth).down :=
  ⟨rfl, fun _ _ eq => Nat.add_left_cancel (congrArg ULift.down eq), fun depth => by
    change n < n + 1 + depth
    omega⟩

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "g" => withLiveOut (P := P) fields a.source

/-- Packet closure is already certified by the reverse checker. If entry
free reads are captures and labelled blocks use the common packet parameter,
every saved register has a type in the input record. Both premises can be
checked on the attached syntax. -/
theorem Lowered.savesCaptures_of_scope
    (entry : ∀ reg ∈ (g).entry.toRegion.fvList, reg.down < n)
    (params : ∀ item ∈ (g).blocks, item.2.param = (freshRegisters n).parameter) :
    a.SavesCaptures :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.saves_captures a entry params

/-- A successful numbered reverse lowering needs no extra packet-profile
certificate. Its entry readback and shared generated parameter establish
that the saved slots are captures. -/
theorem Lowered.savesCaptures_of_lowerFresh [DecidableEq P.Instr] (internal : Fin blocks → K)
    (accepted : lowerFresh internal context exits external fields code = some a) :
    a.SavesCaptures :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.saves_captures_of_lowerFresh a internal accepted

theorem Lowered.synthesizeProfile_eq (R : Fin blocks → Ty κ) (saved : a.SavesCaptures) :
    a.synthesizeProfile R = some (a.packetProfile R saved) :=
  dite_eq_left saved

/-- Successful readback of the actual compiler output and the local
entry and block checks suffice to construct its admission. The only
internal profiles used here are the synthesized packet types. -/
def Lowered.admitOfChecks [DecidableEq κ] (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    {compiled : FiniteCFG P.Instr (CFG.Cyclic.Versioning.compile g).blocks.length exits.length n}
    (readback : NamedFlat.compile g exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some compiled)
    (entry : checkBody (SSA.FiniteSum.append (a.packetProfile R saved)
      (LiveOut.exitInterface (numberedInterface context exits external) fields).external)
      context compiled.entry = true)
    (rows : ∀ i, checkBody (SSA.FiniteSum.append (a.packetProfile R saved)
        (LiveOut.exitInterface (numberedInterface context exits external) fields).external)
      (.snoc context (a.packetProfile R saved i)) (compiled.block i) = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  ⟨⟨g, SSA.ofElaborated _ readback
    ⟨checkBody_sound _ _ _ entry, fun i => checkBody_sound _ _ _ (rows i)⟩, rfl⟩, rfl⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
