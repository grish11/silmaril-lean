module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Straight.Table
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Straight.Values

/-! # Admission of reverse lowering with saved entry captures -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

/-- Successful source checks give packet closure, exact readback and
pointwise typing for the actual empty-record versioner. -/
theorem packetLocalSource_sound {Base V K : Type u} {F : Type v} {n : Nat}
    [DecidableEq Base] [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    (graph : CFG V K F) (names : Fin n → V) (ctx : BoundCtx (Ty Base) n)
    (exits : List K) (external : Fin exits.length → Ty Base)
    (R : Fin (CFG.Cyclic.Versioning.compilePacketLocal graph).blocks.length → Ty Base)
    (checked : packetLocalSourceChecks graph names ctx exits external R = true) :
    CFG.Cyclic.RoundTrip.PacketClosed graph ∧
      ∃ table, NamedFlat.elaborate (CFG.Cyclic.Versioning.compilePacketLocal graph) exits
          (fun i => (names i, 0)) = some table ∧
        let profile := fun i => Ty.product (R i) .unit
        let types := SSA.FiniteSum.append profile external
        checkBody types ctx table.entry = true ∧
          ∀ i, checkBody types (.snoc ctx (profile i)) (table.block i) = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.packetLocalSource_sound
    graph names ctx exits external R checked

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => CFG.Cyclic.Versioning.compile attached
local notation "exitTypes" => Interface.external
  (LiveOut.exitInterface (numberedInterface context exits external) fields)

/-- In a closed entry interface, every saved field of a checked fresh
lowering would have to name a slot in the empty capture context. -/
theorem empty_of_no_captures (closed : n = 0) (saved : a.SavesCaptures) :
    ∀ i, a.savedRegisters i = [] :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.empty_of_no_captures a closed saved

variable [DecidableEq κ]

/-- Source checks suffice for exact scoped readback and typing of the
opt-in compiler at the original argument types paired with unit. -/
theorem compiled_success_packetLocal (R : Fin blocks → Ty κ) (checked : packetLocalChecks a R = true) :
    ∃ table, NamedFlat.elaborate (CFG.Cyclic.Versioning.compilePacketLocal attached) exits
        (fun i : Fin n => ((⟨i.val⟩ : Register), 0)) = some table ∧
      let types := SSA.FiniteSum.append (packetLocalProfile a R) exitTypes
      checkBody types context table.entry = true ∧
        ∀ i, checkBody types (.snoc context (packetLocalProfile a R i)) (table.block i) = true :=
  (packetLocalSource_sound attached (fun i : Fin n => (⟨i.val⟩ : Register)) context exits exitTypes
    (fun i => R (Fin.cast (packetLocalCount a) i)) checked).2

/-- The actual compiler reads back and typechecks when every destination
uses its declared projection of the entry slots and each block can supply
the saved slots required by all its outgoing jumps. -/
theorem compiled_success_projected (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (entrySlots : List (Fin n)) (layouts : Fin (versioned).blocks.length → List (Fin n))
    (layout : ∀ i, a.savedRegisters i = (layouts i).map (fun j => (⟨j.val⟩ : Register)))
    (projections : ∀ i, List.Sublist (layouts i) entrySlots)
    (kept : keepsEntryCaptures a entrySlots = true)
    (edges : checksCaptureEdges a layouts = true) (checked : checks a R = true) :
    ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.compiled_success_projected
    a R saved entrySlots layouts layout projections kept edges checked

/-- The source-local checks suffice for scoped readback and typing of the
actual versioned table at the synthesized profile. Each block saves the
same list of unchanged numbered entry slots, in the compiled order. The
original entry and block checks use the unversioned packet types. -/
theorem compiled_success_captures (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slots : List (Fin n))
    (layout : ∀ i, a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register)))
    (kept : keepsEntryCaptures a slots = true) (checked : checks a R = true) :
    ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.compiled_success_captures
    a R saved slots layout kept checked

/-- Source-local checks suffice for successful scoped readback of the actual
versioned program and all its typing checks. The profile is the one computed
by the numbered reverse lowerer. Internal edges can revisit any block. -/
theorem compiled_success (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  compiled_success_captures a R saved [] empty rfl checked

/-- Source-local readback and typing for one common saved entry field.
The compiled slots identify the field at every destination, and the attached
source leaves that register alone in every body. Its type comes from the
selected position in the original capture context. -/
theorem compiled_success_capture (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Fin n) (layout : ∀ i, a.savedRegisters i = [⟨slot.val⟩])
    (kept : keepsEntryCapture a slot = true) (checked : checks a R = true) :
    ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  compiled_success_captures a R saved [slot] layout (by simpa [keepsEntryCaptures] using kept) checked

private def admitFromReadback (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (success : ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  let read := NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register))
  have found : read.isSome := Option.isSome_iff_exists.mpr (success.imp fun _ h => h.1)
  let table := read.get found
  let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
  have typed : checkBody new context table.entry = true ∧
      ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
    obtain ⟨_, eq, checks⟩ := success
    simpa only [table, read, Option.get_of_eq_some found eq] using checks
  a.admitOfChecks R saved (Option.some_get found).symm typed.1 typed.2

/-- Admit the actual scoped compiler result using the derived checks. -/
def admit (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  admitFromReadback a R saved (compiled_success a R saved empty checked)

omit [DecidableEq κ] in
/-- Layouts of numbered slots witness the synthesized profile's capture bound. -/
theorem savesCaptures_of_layouts (layouts : Fin (versioned).blocks.length → List (Fin n))
    (layout : ∀ i, a.savedRegisters i = (layouts i).map (fun j => (⟨j.val⟩ : Register))) :
    a.SavesCaptures := by
  intro i reg mem
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp (layout i ▸ mem)
  exact j.isLt

omit [DecidableEq κ] in
/-- A common layout of numbered slots witnesses the profile's capture bound. -/
theorem savesCaptures_of_layout (slots : List (Fin n))
    (layout : ∀ i, a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register))) : a.SavesCaptures :=
  savesCaptures_of_layouts a (fun _ => slots) layout

/-- Admit the actual compiler result at the supplied per-destination
projections, keeping the original entry and ordered exits. -/
def admitWithProjections (R : Fin blocks → Ty κ)
    (entrySlots : List (Fin n)) (layouts : Fin (versioned).blocks.length → List (Fin n))
    (layout : ∀ i, a.savedRegisters i = (layouts i).map (fun j => (⟨j.val⟩ : Register)))
    (projections : ∀ i, List.Sublist (layouts i) entrySlots)
    (kept : keepsEntryCaptures a entrySlots = true)
    (edges : checksCaptureEdges a layouts = true) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  let saved := savesCaptures_of_layouts a layouts layout
  admitFromReadback a R saved
    (compiled_success_projected a R saved entrySlots layouts layout projections kept edges checked)

/-- Admit the actual compiler result at the original entry and exit
interface, using the same ordered capture layout at every destination. -/
def admitWithCaptures (R : Fin blocks → Ty κ)
    (slots : List (Fin n))
    (layout : ∀ i, a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register)))
    (kept : keepsEntryCaptures a slots = true) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  let saved := savesCaptures_of_layout a slots layout
  admitFromReadback a R saved (compiled_success_captures a R saved slots layout kept checked)

/-- Admit a capture-carrying table at the original entry and exit interface. -/
def admitWithCapture (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Fin n) (layout : ∀ i, a.savedRegisters i = [⟨slot.val⟩])
    (kept : keepsEntryCapture a slot = true) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  admitFromReadback a R saved (compiled_success_capture a R saved slot layout kept checked)

section Values

open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)

variable [AtomValues κ]

local notation "C" => AtomValues.carrier (κ := κ)
local notation "Input" => Ty.denote C (Region.packedInputType context.toList)

omit [DecidableEq κ] in
/-- The version-zero capture is the same tagged field of the supplied
typed entry record as in the mutable store. -/
theorem capture_at_version_zero (slot : Fin n) (x : Input) :
    store (fun i : Fin n => ((⟨i.val⟩ : Register), 0)) context x (⟨slot.val⟩, 0) =
      inputEnv context x slot.val :=
  (store_version_zero (fun i : Fin n => (⟨i.val⟩ : Register)) context x ⟨slot.val⟩).trans
    (store_at _ (fun _ _ eq => Fin.ext (congrArg ULift.down eq)) context x slot)

omit [DecidableEq κ] in
/-- Encode the actual jump, retaining the caller's slot order and the tags
of its supplied input fields. Agreement is required for each saved store
slot at this transfer. -/
theorem encode_captures {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr)
    (slots : List (Fin n)) (x : Input) (transfer : CFG.Cyclic.Transfer Register K (Value (Sigma C)))
    (route : CFG.Cyclic.Versioning.destinations attached transfer.1 =
      some (slots.map (fun j => (⟨j.val⟩ : Register))))
    (agrees : ∀ j ∈ slots, transfer.2.2 ⟨j.val⟩ = inputEnv context x j.val) :
    CFG.Cyclic.Versioning.encode (treeModel M.raw) attached transfer =
      (transfer.1, .pair transfer.2.1
        (slots.foldr (fun j tail => .pair (inputEnv context x j.val) tail) .unit)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.encode_captures a M slots x transfer route agrees

omit [DecidableEq κ] in
/-- For a transfer whose saved register still holds the entry field, the
actual versioner's packet contains that tagged field after the argument. -/
theorem encode_capture {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr)
    (slot : Fin n) (x : Input) (transfer : CFG.Cyclic.Transfer Register K (Value (Sigma C)))
    (route : CFG.Cyclic.Versioning.destinations attached transfer.1 = some [⟨slot.val⟩])
    (agrees : transfer.2.2 ⟨slot.val⟩ = inputEnv context x slot.val) :
    CFG.Cyclic.Versioning.encode (treeModel M.raw) attached transfer =
      (transfer.1, .pair transfer.2.1 (.pair (inputEnv context x slot.val) .unit)) :=
  encode_captures a M [slot] x transfer route (fun j mem => by
    cases List.mem_singleton.mp mem
    exact agrees)

end Values

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
