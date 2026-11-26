module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Flat.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Institution.Defs

/-! # Admit an independently witnessed LetCase term as named packet-local RTL -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed

open LambdaSSA (Region)
open LambdaSSA.Acyclic
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Isotope.Institution.LetCase.WeakITree (Equation closedOperand)

universe u v

variable {κ K : Type (u + 1)} [DecidableEq K] {n : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "exitList" => List.ofFn exitTypes
local notation "B" => Region.packedExitType exitList

variable {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))}

/-- The actual table handed to the named emitter. The selected caller
slots are carried only on internal edges, in the specified order. -/
def flatList (g : ResultGrammar (L := exitList) source) (slots : List (Fin n)) :
    LambdaSSA.FiniteCFG P.Instr (g.toTable.size + 1) exits.length n :=
  Capture.Carry.graphList (g.toTable.toFlat List.length_ofFn) slots

/-- The exact internal packet family for the table handed to the emitter. -/
def packetTypesList (g : ResultGrammar (L := exitList) source) (slots : List (Fin n)) :
    Fin (g.toTable.size + 1) → Ty κ :=
  Capture.Carry.packetTypesList g.toTable.table.types context slots

abbrev flat (g : ResultGrammar (L := exitList) source) (slot : Option (Fin n)) :=
  flatList g slot.toList

abbrev packetTypes (g : ResultGrammar (L := exitList) source) (slot : Option (Fin n)) :=
  packetTypesList g slot.toList

/-- Retain the emission, its literal attached readback, and the actual
opt-in versioned admission at the original public interface. -/
structure CompiledList (g : ResultGrammar (L := exitList) source) (slots : List (Fin n)) where
  lowered : Lowered ports fields (flatList g slots)
  admission : Admission lowered
  ranked : admission.acyclicCheck = true

/-- The empty and singleton capture layouts of the original API. -/
abbrev Compiled (g : ResultGrammar (L := exitList) source) (slot : Option (Fin n) := none) :=
  CompiledList g slot.toList

/-- Check typing, actual opt-in reversion and entry-reachable rank after emission. -/
def checkListAdmission [DecidableEq κ] (g : ResultGrammar (L := exitList) source)
    {slots : List (Fin n)} (lowered : Lowered ports fields (flatList g slots)) :
    Option (CompiledList g slots) :=
  (checkRanked lowered (packetTypesList g slots)).map (fun c => ⟨c.lowered, c.admission, c.ranked⟩)

abbrev checkAdmission [DecidableEq κ] (g : ResultGrammar (L := exitList) source)
    {slot : Option (Fin n)} (lowered : Lowered ports fields (flat g slot)) :
    Option (Compiled g slot) :=
  checkListAdmission g (slots := slot.toList) lowered

/-- Run the existing reverse emitter and checkers on the numbered witness. -/
def compile? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (labels : Fin (g.toTable.size + 1) → K) : Option (Compiled g) := do
  let lowered ← lowerFresh labels context exits external fields (flatList g [])
  checkListAdmission g (slots := []) lowered

/-- Carry the ordered caller slots explicitly in each internal packet before
running the same emitter and checkers. The register plan must reproduce the
selected live-out reads exactly after the row's product decoders. -/
def compileCarryList? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (slots : List (Fin n)) (registers : Registers Register) (labels : Fin (g.toTable.size + 1) → K) :
    Option (CompiledList g slots) :=
  (compileFlatCarry? (context := context) (external := external) (fields := fields) (flat g none) g.toTable.table.types slots registers labels).map
    (fun c => ⟨c.lowered, c.admission, c.ranked⟩)

/-- Specialize the ordered adapter to one caller slot. -/
def compileCarry? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (slot : Fin n) (registers : Registers Register) (labels : Fin (g.toTable.size + 1) → K) :
    Option (Compiled g (some slot)) :=
  compileCarryList? g [slot] registers labels

/-- Infer the shared layout from the numbered typed table, including any
reads in discriminator expressions and outward live-out payloads. -/
def inferredSlots (g : ResultGrammar (L := exitList) source) : List (Fin n) :=
  Capture.Carry.inferSlots (flat g none)

/-- Lower with the inferred list. Labels and registers are still supplied
by the caller, and the existing checker decides admission. -/
def compileInferred? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (registers : Registers Register) (labels : Fin (g.toTable.size + 1) → K) :
    Option (CompiledList g (inferredSlots g)) :=
  (compileFlatInferred? (context := context) (external := external) (fields := fields) (flat g none) g.toTable.table.types registers labels).map
    (fun c => ⟨c.lowered, c.admission, c.ranked⟩)

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

/-- Native evaluation of the original written term at the shared caller record. -/
noncomputable def sourceTree (M : Model (κ := κ) Events P.Instr) (source : Operand P.Instr context B)
    (x : Record.Input context) : ModelTree Events (Ty.denote C B) :=
  source.2.denote (Ty.denote C) ⟨M.instructions.denote⟩ (fun y => y.elim) (Record.field context x)

section Equation

variable {P : FlatInstitution.Signature.{u, u+1} κ}
  {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))} {g : ResultGrammar source}

/-- Compare the written source with the LetCase expansion of the actual
admitted packed graph, using the existing exact institution's sentence. -/
noncomputable def CompiledList.equation {slots : List (Fin n)} (c : CompiledList g slots) : Equation P :=
  ⟨⟨n, context, B⟩, closedOperand (P := P) source.2,
    closedOperand (P := P) (c.admission.letCase c.ranked).2⟩

noncomputable abbrev Compiled.equation {slot : Option (Fin n)} (c : Compiled g slot) : Equation P :=
  CompiledList.equation c

end Equation

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed
