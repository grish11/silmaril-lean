module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (Region FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

universe u v
variable {κ V Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context} {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)

omit [DecidableEq Reg] in
theorem observe_packed (a : Admission P I fields C) (M : Model (κ := κ) Events P.Instr)
    (record : Input I.context) (ambient : Env (Sigma Atoms)) :
    a.observe M record =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry a.typed).code := by
  let input := C.store record
  let store := Phi.inputEnv (treeModel M.raw) input
  have agrees (i : Fin I.slots) : NamedFlat.Entry.inputEnv I.context record i.val = store (C.names i, 0) := by
    simpa [input, store, captureEnv, i.isLt, Phi.inputEnv, Phi.liftStore, treeModel] using
      C.inputEnv_eq record i
  have openTree := NamedFlat.compile_run_tree M.raw (Phi.OrderedExits.lower a.source)
    I.exits C.names a.elaborated store (NamedFlat.Entry.inputEnv I.context record) agrees
  have lexical := Phi.OrderedExits.run_commutes (treeModel M.raw) ⟨fun _ _ => rfl⟩ a.source input
  calc
    _ = ((Phi.OrderedExits.run (treeModel M.raw) a.source input >>= fun p => pure (treeExitNumber I.exits p)) >>=
        fun p => pure (FiniteCFG.packedTreeOutput p)) := by
      simp only [Admission.observe, input, bind_assoc, pure_bind]
    _ = (region M.raw (NamedFlat.Entry.inputEnv I.context record) a.code.erase >>=
        fun p => pure (FiniteCFG.packedTreeOutput p)) :=
      congrArg (fun t => t >>= fun p => pure (FiniteCFG.packedTreeOutput p))
        ((congrArg (fun t => t >>= fun p => pure (treeExitNumber I.exits p)) lexical).trans openTree)
    _ = _ := by
      change _ = region M.raw (extend ambient (encodeValue Atoms _ record))
        ((FiniteCFG.packedExecutionRegion a.typed).packInputsDestructure I.context.toList)
      rw [← NamedFlat.Entry.inputEnv_packet I.context record,
        NamedFlat.Capture.packed_context_tree M.raw a.typed ambient]
      rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
