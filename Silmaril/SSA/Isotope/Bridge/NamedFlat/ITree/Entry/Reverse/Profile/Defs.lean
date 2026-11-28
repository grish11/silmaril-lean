module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs

/-! # Synthesize packet types for reverse lowering with numbered registers -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.SSA.LambdaRTL.CFG.Cyclic

universe u v

abbrev Register := ULift.{u + 1} Nat

variable {κ K : Type (u + 1)} {n blocks : Nat}

/-- Use the newest-first positional index as each input register number. -/
abbrev numberedInterface (context : BoundCtx (Ty κ) n) (exits : List K)
    (external : Fin exits.length → Ty κ) : Interface κ Register K :=
  ⟨n, context, fun i => ⟨i.val⟩, fun _ _ eq => Fin.ext (congrArg ULift.down eq), exits, external⟩

/-- Keep the packet register and all local depths outside the capture range.
Local depths can recur in distinct blocks or mutually exclusive arms. -/
def freshRegisters (captures : Nat) : Registers Register :=
  ⟨⟨captures⟩, fun depth => ⟨captures + 1 + depth⟩⟩

variable [DecidableEq K] {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}


/-- Use the existing reverse checker with the deterministic allocation. -/
def lowerFresh [DecidableEq P.Instr] (internal : Fin blocks → K)
    (context : BoundCtx (Ty κ) n) (exits : List K) (external : Fin exits.length → Ty κ)
    (fields : K → List (Register × Ty κ)) (code : FiniteCFG P.Instr blocks exits.length n) :
    Option (Lowered (numberedInterface context exits external) fields code) :=
  lowerChecked (numberedInterface context exits external) fields (freshRegisters n) internal code

variable (a : Lowered (numberedInterface context exits external) fields code)

/-- Internal indices are preserved by the actual versioner's block map. -/
theorem Lowered.reversionCount : (Versioning.compile (withLiveOut (P := P) fields a.source)).blocks.length =
    blocks :=
  (List.length_map _).trans a.count

/-- Read the slot order from the attached graph, including the versioner's
exclusion of the destination's parameter. -/
def Lowered.savedRegisters (i : Fin (Versioning.compile (withLiveOut (P := P) fields a.source)).blocks.length) :
    List Register :=
  let g := withLiveOut (P := P) fields a.source
  Versioning.slots g g.blocks[(Fin.cast (List.length_map _) i)].2

/-- Each additional field of the versioner's destination packet is a
numbered entry capture. Check this on the actual saved-register lists. -/
def Lowered.SavesCaptures : Prop :=
  ∀ i, ∀ reg ∈ a.savedRegisters i, reg.down < n

instance : Decidable a.SavesCaptures := inferInstanceAs
  (Decidable (∀ i, ∀ reg ∈ a.savedRegisters i, reg.down < n))

/-- Build the original destination argument followed by the typed record
in the actual versioner's slot order. -/
def Lowered.packetProfile (R : Fin blocks → Ty κ) (h : a.SavesCaptures)
    (i : Fin (Versioning.compile (withLiveOut (P := P) fields a.source)).blocks.length) : Ty κ :=
  let slots := (a.savedRegisters i).attach.map fun reg =>
    (reg.val, context.get ⟨reg.val.down, h i reg.val reg.property⟩)
  .product (R (Fin.cast a.reversionCount i)) (LiveOut.recordType slots)

/-- Compute the profile without a caller-supplied reversion packet type.
Failure identifies a slot outside the numbered capture range. -/
def Lowered.synthesizeProfile (R : Fin blocks → Ty κ) :
    Option (Fin (Versioning.compile (withLiveOut (P := P) fields a.source)).blocks.length → Ty κ) :=
  if h : a.SavesCaptures then some (a.packetProfile R h) else none

/-- Re-admit the actual lowered graph using its synthesized profile.
The existing elaboration and exact type check remain the final gates. -/
def Lowered.reAdmit [DecidableEq κ] (R : Fin blocks → Ty κ) :
    Option (LiveOut.Admission P (numberedInterface context exits external) fields a.source) :=
  (a.synthesizeProfile R).bind (LiveOut.admit (P := P) (numberedInterface context exits external) fields a.source)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
