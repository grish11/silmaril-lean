module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Thms

/-! # LetCase after the actual packet-local compilation -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Acyclic
open LambdaSSA.Acyclic.Positional
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LetIter.ProofRelevant.Semantics (InstructionModel)

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}
  {a : Lowered (numberedInterface context exits external) fields code}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "B" => Region.packedExitType (List.ofFn exitTypes)

/-- Check the rows reachable from the actual generated entry. All written
entry branches contribute roots. The table and its interface stay intact. -/
def Admission.acyclicCheck (admission : Admission a) : Bool :=
  FlatLetCase.entryCheck admission.versioned.table.code

/-- An existing whole-table rank certificate still admits the expansion. -/
theorem Admission.acyclicCheck_of_all (admission : Admission a)
    (ranked : Rank.check (FlatLetCase.localTargets admission.versioned.table.code) = true) :
    admission.acyclicCheck = true :=
  Rank.checkFrom_of_check _ _ ranked

/-- Expand the admitted result through the existing structured acyclic
grammar and LetCase translation. -/
noncomputable def Admission.letCase (admission : Admission a) (ranked : admission.acyclicCheck = true) :
    Operand P.Instr context B :=
  FlatLetCase.toLetCaseReachable admission.versioned.table.typed ranked

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

/-- Use exactly the typed primitives of the ordered model, and project the
same supplied record into the native LetCase bound environment. -/
noncomputable def Admission.letCaseTree (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (ranked : admission.acyclicCheck = true) (x : Record.Input context) : ModelTree Events (Ty.denote C B) :=
  (admission.letCase ranked).2.denote (Ty.denote C)
    ⟨M.instructions.denote⟩ (fun free => free.elim) (Record.field context x)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
