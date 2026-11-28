module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms

/-! # Packet-local admission of a supplied named mutable graph -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ}

/-- Exact scoped elaboration of the actual empty-record versioner, together
with packet closure after the selected live-out reads are attached. -/
structure Admission (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) (source : CFG V K P.Instr) where
  closed : RoundTrip.PacketClosed (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source)
  versioned : SSA P (exitInterface I fields).version
  compiled : versioned.source = Versioning.compilePacketLocal
    (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source)

/-- Use the existing packed dispatcher at the original caller context and
ordered outward payloads enlarged by the selected live-out fields. -/
def Admission.program {I : Interface κ V K} {fields : K → List (V × Ty κ)}
    {source : CFG V K P.Instr} (a : Admission P I fields source) :
    Program P.Instr (Region.packedInputType I.context.toList)
      (Region.packedExitType (List.ofFn (Interface.external (exitInterface I fields)))) :=
  Program.ofCFGEntry a.versioned.table.typed

variable (I : Interface κ V K) (fields : K → List (V × Ty κ)) (source : CFG V K P.Instr)

local notation "attached" => CFG.Cyclic.LiveOut.attach (fun k => List.map Prod.fst (fields k)) source
local notation "projected" => exitInterface I fields
local notation "target" => Versioning.compilePacketLocal attached

/-- Live-out attachment and packet-local versioning preserve the row count. -/
theorem reversionCount : (target).blocks.length = source.blocks.length :=
  (List.length_map _).trans (List.length_map _)

variable [DecidableEq κ]

/-- Check the attached entry and rows at their original argument types.
The entry may read the declared names. Each row starts at its own parameter. -/
def check (R : Fin source.blocks.length → Ty κ) : Bool :=
  Reverse.Straight.packetLocalSourceChecks attached I.names I.context I.exits (projected).external
    (fun i => R (Fin.cast (reversionCount fields source) i))

/-- Derive the exact versioner readback, typing and closure from the same
source check. The installed argument profile pairs each argument with unit. -/
def admitOfCheck (R : Fin source.blocks.length → Ty κ)
    (checked : check (P := P) I fields source R = true) : Admission P I fields source :=
  let read := NamedFlat.elaborate target I.exits (fun i => (I.names i, 0))
  let argument := fun i => R (Fin.cast (reversionCount fields source) i)
  let sound := Reverse.Straight.packetLocalSource_sound attached I.names I.context
    I.exits (projected).external argument checked
  have found : read.isSome := Option.isSome_iff_exists.mpr (sound.2.imp fun _ h => h.1)
  let table := read.get found
  have typed : table.HasType I.context (fun i => .product (argument i) .unit) (projected).external := by
    obtain ⟨code, eq, entry, rows⟩ := sound.2
    have witness : code.HasType I.context (fun i => .product (argument i) .unit) (projected).external :=
      ⟨NamedFlat.checkBody_sound _ _ _ entry, fun i => NamedFlat.checkBody_sound _ _ _ (rows i)⟩
    simpa only [table, Option.get_of_eq_some found (show read = some code from eq)] using witness
  ⟨sound.1, SSA.ofElaborated target (Option.some_get found).symm typed, rfl⟩

/-- Admit a supplied named table. The executable check accepts cyclic edges
using the same first-match label numbering as elaboration. -/
def admit (R : Fin source.blocks.length → Ty κ) : Option (Admission P I fields source) :=
  if checked : check (P := P) I fields source R = true then
    some (admitOfCheck I fields source R checked)
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
