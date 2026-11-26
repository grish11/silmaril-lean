module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms

/-! # Admitted named comparisons at a fixed typed entry and exit interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry

open CategoryTheory
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)

universe u v
variable {κ : Type (u + 1)} {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P Q : FlatInstitution.Signature.{u, v} κ}

/-- The names of the supplied entry fields are distinct. The exit list supplies
the same ordered payload interface to both sides of a named comparison. -/
structure Interface (κ V K : Type (u + 1)) where
  slots : Nat
  context : BoundCtx (Ty κ) slots
  names : Fin slots → V
  distinct : Function.Injective names
  exits : List K
  external : Fin exits.length → Ty κ

variable (I : Interface κ V K)

/-- The typed lexical interface for the actual cyclic versioner. -/
def Interface.version (I : Interface κ V K) : Interface κ (V × Nat) K :=
  ⟨I.slots, I.context, fun i => (I.names i, 0),
    fun _ _ eq => I.distinct (congrArg Prod.fst eq), I.exits, I.external⟩

/-- An ordinary named lexical table with its actual admitted flat code
and the chosen exact internal typing profile. -/
structure SSA (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K) where
  source : CFG V K P.Instr
  table : EntryInstitution.Table P I.context I.external
  count : source.blocks.length = table.blocks
  accepted : elaborateAt source I.exits I.names table.blocks count = some table.code

variable {I}

/-- Package the existing elaboration equation and typing proof. -/
def SSA.ofElaborated (g : CFG V K P.Instr)
    {code : FiniteCFG P.Instr g.blocks.length I.exits.length I.slots}
    {R : Fin g.blocks.length → Ty κ}
    (accepted : elaborate g I.exits I.names = some code)
    (typed : code.HasType I.context R I.external) : SSA P I :=
  ⟨g, .ofTyped typed, rfl, (elaborateAt_eq g I.exits I.names).trans accepted⟩

/-- Executable admission at the given internal profile. -/
def SSA.admit [DecidableEq κ] (g : CFG V K P.Instr) (R : Fin g.blocks.length → Ty κ) :
    Option (SSA P I) :=
  match accepted : elaborate g I.exits I.names with
  | none => none
  | some code =>
    if checked : check code I.context R I.external = true then
      some (.ofElaborated g accepted (check_sound code I.context R I.external checked))
    else none

/-- Change only the primitive alphabet and transport the exact certificate
at the original internal profile. -/
def SSA.map (a : SSA P I) (f : P ⟶ Q) : SSA Q I :=
  let opcode := f.toSignatureMap.instr
  have count : (a.source.mapOp opcode).blocks.length = a.table.blocks := by
    simpa only [CFG.mapOp, List.length_map] using a.count
  ⟨a.source.mapOp opcode, a.table.map f, count, by
    change elaborateAt (a.source.mapOp opcode) I.exits I.names a.table.blocks count =
      some (a.table.code.mapInstr opcode)
    rw [elaborateAt_mapOp opcode a.source I.exits I.names _ a.count count, a.accepted]
    rfl⟩

/-- A mutable source with a certified open elaboration of the actual
block-local SSA produced by cyclic versioning. -/
structure RTL (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K) where
  source : CFG V K P.Instr
  versioned : SSA P I.version
  compiled : versioned.source = CFG.Cyclic.Versioning.compile source

/-- Use the actual result of the existing checker for versioned named code. -/
def RTL.admit [DecidableEq κ] (g : CFG V K P.Instr)
    (R : Fin (CFG.Cyclic.Versioning.compile g).blocks.length → Ty κ) : Option (RTL P I) :=
  (compileTyped g I.exits I.names I.context R I.external).map fun certificate =>
    ⟨g, .ofElaborated _ certificate.property.1 certificate.property.2, rfl⟩

def RTL.map (a : RTL P I) (f : P ⟶ Q) : RTL Q I :=
  ⟨a.source.mapOp f.toSignatureMap.instr, a.versioned.map f, by
    change a.versioned.source.mapOp _ = _
    rw [a.compiled, CFG.Cyclic.Versioning.compile_mapOp]⟩

/-- Each side carries its own named syntax and admission certificate. -/
abbrev SSASentence (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K) :=
  SSA P I × SSA P I

abbrev RTLSentence (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K) :=
  RTL P I × RTL P I

def toFlat (s : SSASentence P I) : EntryInstitution.Sentence P I.context :=
  ⟨I.exits.length, I.external, s.1.table, s.2.table⟩

def toSSA (s : RTLSentence P I) : SSASentence P I.version :=
  (s.1.versioned, s.2.versioned)

variable [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

/-- Evaluate the named lexical runner at the projected input, numbering and
tagging its returns in the declared packed exit interface. -/
noncomputable def SSA.observe (M : Model (κ := κ) Events P.Instr) (a : SSA P I) (x : Ty.denote C A) :=
  CFG.Cyclic.runSSA (treeModel M.raw) a.source (store I.names I.context x) >>= fun p =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber I.exits p))

/-- Evaluate the mutable runner at the same projected input. The observation
keeps the external label and payload, and drops the final mutable store. -/
noncomputable def RTL.observe (M : Model (κ := κ) Events P.Instr) (a : RTL P I) (x : Ty.denote C A) :=
  CFG.Cyclic.run (treeModel M.raw) a.source (store I.names I.context x) >>= fun p =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber I.exits (obs p)))

def ssaSatisfies (M : Model (κ := κ) Events P.Instr) (s : SSASentence P I) : Prop :=
  ∀ x, TraceLE (s.1.observe M x) (s.2.observe M x)

def rtlSatisfies (M : Model (κ := κ) Events P.Instr) (s : RTLSentence P I) : Prop :=
  ∀ x, TraceLE (s.1.observe M x) (s.2.observe M x)

end Silmaril.Isotope.Bridge.NamedFlat.Entry
