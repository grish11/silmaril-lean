module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Acyclic
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region term)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Isotope.Semantics (encodeValue)
open Morphism.CaseSSA (erase)

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}
  {a : Lowered (numberedInterface context exits external) fields code}
  [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "A" => Region.packedInputType context.toList
local notation "B" => Region.packedExitType (List.ofFn (Interface.external (LiveOut.exitInterface ports fields)))
local notation "C" => AtomValues.carrier (κ := κ)

theorem packed_letCase_tree (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (ranked : admission.acyclicCheck = true) (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) admission.program.code =
      (admission.letCaseTree M ranked x >>= fun b => pure (0, encodeValue C B b)) := by
  let typed := admission.versioned.table.typed
  let env := inputEnv context x
  have packed :
      region M.raw (extend ambient (encodeValue C A x)) admission.program.code =
      (region M.raw env admission.versioned.table.code.erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) := by
    rw [← inputEnv_packet]
    exact Capture.packed_context_tree M.raw typed ambient env
  have expanded :
      term M.raw env (erase (admission.letCase ranked).1) =
      (region M.raw env admission.versioned.table.code.erase >>= fun p =>
        pure (Region.packedExitValue p.1 p.2)) :=
    FlatLetCase.toLetCaseReachable_tree M.raw typed ranked env
  have letcase :
      (admission.letCaseTree M ranked x >>= fun b => pure (encodeValue C B b)) =
        term M.raw env (erase (admission.letCase ranked).1) :=
    FlatLetCase.denote_tree ⟨M.instructions.denote⟩ M.raw M.compatible _ _ _
      (Record.inputEnv_field context x)
  calc
    _ = (term M.raw env (erase (admission.letCase ranked).1) >>= fun value => pure (0, value)) := by
      rw [expanded, packed, bind_assoc]
      simp only [pure_bind, FiniteCFG.packedTreeOutput]
    _ = _ := by rw [← letcase, bind_assoc]; simp only [pure_bind]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
