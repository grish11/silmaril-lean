module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Witnessed.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocalLetCaseWitnessed

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed

open LambdaSSA (Region)
open LambdaSSA.Acyclic
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v

variable {κ K : Type (u + 1)} [DecidableEq K] {n : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)} [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "A" => Region.packedInputType context.toList
local notation "exitList" => List.ofFn exitTypes
local notation "B" => Region.packedExitType exitList
local notation "C" => AtomValues.carrier (κ := κ)

variable {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))} {g : ResultGrammar source} {slots : List (Fin n)}

omit [DecidableEq K] [AtomValues κ] in
/-- The pre-reversion table is typed at the original entry and exit
interfaces. Carrying caller slots changes only the internal packet family. -/
theorem flatList_hasType (g : ResultGrammar source) (slots : List (Fin n)) :
    (flatList g slots).HasType context (packetTypesList g slots) exitTypes :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.flatList_hasType g slots

omit [DecidableEq K] [AtomValues κ] in
theorem flat_hasType (g : ResultGrammar source) (slot : Option (Fin n)) :
    (flat g slot).HasType context (packetTypes g slot) exitTypes :=
  flatList_hasType g slot.toList

omit [DecidableEq K] [AtomValues κ] in
/-- The actual table passed to the inferred-layout emitter has packet-only
rows before named emission or any allocation, typing, or rank check. -/
theorem inferred_packetOnly (g : ResultGrammar source) (row : Fin (g.toTable.size + 1)) :
    ((flatList g (inferredSlots g)).block row).erase.Scoped (g.toTable.size + 1 + exits.length) 1 :=
  Capture.Carry.infer_packetOnly _ row

/-- Run the emitted mutable table at the original typed caller record and
observe the same tagged result, including the specified final-store fields. -/
theorem CompiledList.named_tree (M : Model (κ := κ) Events P.Instr) (c : CompiledList g slots) (x : Record.Input context) :
    (sourceTree M source x >>= fun b => pure (0, encodeValue C B b)) =
      LiveOut.observe M ports fields c.lowered.source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.named_tree M c x

/-- The packed interpreter of the actual versioned named table agrees
with native evaluation of the original written LetCase term. -/
theorem CompiledList.packed_tree (M : Model (κ := κ) Events P.Instr) (c : CompiledList g slots)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code =
      (sourceTree M source x >>= fun b => pure (0, encodeValue C B b)) :=
  (c.admission.packed_tree M x ambient).trans (c.named_tree M x).symm

/-- The same reversion equation in the existing typed packed denotations. -/
theorem CompiledList.packed_eq (M : Model (κ := κ) Events P.Instr) (c : CompiledList g slots) :
    (Program.ofCFGEntry (g.toTable.toFlat_hasType (D := exitTypes))).denote M = c.admission.program.denote M :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.packed_eq M c

variable {slot : Option (Fin n)}

theorem Compiled.named_tree (M : Model (κ := κ) Events P.Instr) (c : Compiled g slot) (x : Record.Input context) :
    (sourceTree M source x >>= fun b => pure (0, encodeValue C B b)) =
      LiveOut.observe M ports fields c.lowered.source x :=
  CompiledList.named_tree M c x

theorem Compiled.packed_tree (M : Model (κ := κ) Events P.Instr) (c : Compiled g slot)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code =
      (sourceTree M source x >>= fun b => pure (0, encodeValue C B b)) :=
  CompiledList.packed_tree M c x ambient

theorem Compiled.packed_eq (M : Model (κ := κ) Events P.Instr) (c : Compiled g slot) :
    (Program.ofCFGEntry (g.toTable.toFlat_hasType (D := exitTypes))).denote M = c.admission.program.denote M :=
  CompiledList.packed_eq M c

section Equation

open Isotope.Institution.LetCase.WeakITree (algebra equationRoom)

variable {P : FlatInstitution.Signature.{u, u+1} κ}
  {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))} {g : ResultGrammar source} {slots : List (Fin n)}

/-- Validate the exact equation from the written term to the re-expanded
actual admission, in every compatible weak-tree model. -/
theorem CompiledList.satisfies (M : Model (κ := κ) Events P.Instr) (c : CompiledList g slots) :
    (equationRoom P).Sat (algebra (P := P) M) c.equation :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.satisfies M c

theorem Compiled.satisfies (M : Model (κ := κ) Events P.Instr) (c : Compiled g slot) :
    (equationRoom P).Sat (algebra (P := P) M) c.equation :=
  CompiledList.satisfies M c

end Equation
end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed
