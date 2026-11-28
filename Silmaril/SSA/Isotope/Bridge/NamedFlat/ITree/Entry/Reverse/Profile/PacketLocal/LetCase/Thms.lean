module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocalLetCase

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Isotope.Semantics (encodeValue)

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

/-- The actual packed program and its expanded native typed LetCase term
compute the same weak tree at the same supplied entry record. -/
theorem Admission.packed_letCase_tree (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (ranked : admission.acyclicCheck = true) (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) admission.program.code =
      (admission.letCaseTree M ranked x >>= fun b => pure (0, encodeValue C B b)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.packed_letCase_tree M admission ranked x ambient

/-- The LetCase route observes the same ordered exits and selected final
store fields as the named mutable route. -/
theorem Admission.letCase_observe (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (ranked : admission.acyclicCheck = true) (x : Record.Input context) (ambient : Env (Sigma C)) :
    (admission.letCaseTree M ranked x >>= fun b => pure (0, encodeValue C B b)) =
      LiveOut.observe M ports fields a.source x :=
  (admission.packed_letCase_tree M ranked x ambient).symm.trans (admission.packed_tree M x ambient)

/-- When the original named table supports suffix lookup, the same square
uses the existing forward CFG runner with its actual final-store projection. -/
theorem Admission.letCase_observe_forward (M : Model (κ := κ) Events P.Instr) (admission : Admission a)
    (ranked : admission.acyclicCheck = true) (forward : CFG.Cyclic.IsForward a.source)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    (admission.letCaseTree M ranked x >>= fun b => pure (0, encodeValue C B b)) =
      (a.source.run (treeModel M.raw) (store (Interface.names ports) context x) >>= fun final =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber exits
          (obs (CFG.Cyclic.LiveOut.project (treeModel M.raw) (fun k => (fields k).map Prod.fst) final))))) := by
  rw [admission.letCase_observe M ranked x ambient]
  simp only [LiveOut.observe, LiveOut.observeRaw, CFG.Cyclic.run_eq_forward (treeModel M.raw) a.source forward]

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
