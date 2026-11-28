module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.ITree.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open NamedFlat (treeExitNumber treeModel)
open NamedFlat.Phi (runTree)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.SSA.LambdaRTL
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
section
variable {Events : Type u → Type u} {V K Base α : Type (u + 1)} {F : Type v} {n : Nat}
  [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
  {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {D : Fin 1 → Ty Base}

private theorem open_run_tree (admitted : Admission source inputs captures β R D)
    (instr : Primitive Events F α) (store : V → Value α) (env : Env α)
    (agrees : ∀ i : Fin n, env i.val = captureEnv captures store i.val) :
    (runTree instr source store >>= fun p => pure (treeExitNumber [none] p)) =
      region instr env admitted.graph.erase :=
  NamedFlat.Phi.run_tree ((CFG.Cyclic.Phi.compile_eq_some_iff _ _).mpr ⟨admitted.wellFormed.normalized, rfl⟩)
    instr store (fun i => (captures i, 0)) admitted.elaborated env
    (fun i => by simpa [captureEnv, i.isLt, CFG.Cyclic.Phi.inputEnv, CFG.Cyclic.Phi.liftStore, treeModel] using agrees i)

end

variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  {I : Captures V β} {Jc : Captures W β} {D : Fin 1 → Ty κ}
  [AtomValues κ] [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "A" => Region.packedInputType β.toList
local notation "Record" => Ty.denote C A

private theorem inputEnv_unit (record : Record) (i : Fin n) (ty : β.get i = .unit) :
    NamedFlat.Entry.inputEnv β record i.val = .unit := by
  induction β with
  | nil => exact i.elim0
  | snoc β T ih =>
    revert ty
    refine Fin.cases ?_ ?_ i
    · intro same
      change T = .unit at same
      subst T
      rfl
    · intro j same
      exact ih record.1 j same

theorem capture_agrees (I : Captures V β) (record : Record) (i : Fin n) :
    NamedFlat.Entry.inputEnv β record i.val = captureEnv I.names (I.store record) i.val := by
  cases h : I.names i with
  | none =>
    simpa [captureEnv, i.isLt, h] using inputEnv_unit record i (I.privateUnit i h)
  | some name =>
    have := NamedFlat.Entry.store_at I.names I.distinct β record i
    simpa [captureEnv, i.isLt, Captures.store, h] using this.symm

theorem observe_entry_of_capture (a : Admitted P I K D) (M : Model (κ := κ) Events P.Instr)
    (record : Record) (ambient : Env (Sigma C)) (store : V → Value (Sigma C))
    (agrees : ∀ i : Fin n, NamedFlat.Entry.inputEnv β record i.val = captureEnv I.names store i.val) :
    PureCapture.sourceObservation M.raw a.source store =
      region M.raw (extend ambient (encodeValue C A record))
        (Program.ofCFGEntry a.admission.typed).code := by
  change _ = region M.raw (extend ambient (encodeValue C A record))
    ((LambdaSSA.FiniteCFG.packedExecutionRegion a.admission.typed).packInputsDestructure β.toList)
  rw [← NamedFlat.Entry.inputEnv_packet β record,
    NamedFlat.Capture.packed_context_tree M.raw a.admission.typed ambient,
    ← open_run_tree a.admission M.raw _ _ agrees, bind_assoc]
  simp only [PureCapture.sourceObservation, pure_bind]

theorem observe_entry (a : Admitted P I K D) (M : Model (κ := κ) Events P.Instr)
    (record : Record) (ambient : Env (Sigma C)) :
    a.observe M record = region M.raw (extend ambient (encodeValue C A record))
      (Program.ofCFGEntry a.admission.typed).code :=
  observe_entry_of_capture a M record ambient (I.store record) (capture_agrees I record)

theorem flat_satisfies (M : Model (κ := κ) Events P.Instr) (s : Sentence P I Jc K J D) :
    EntryInstitution.Satisfies Events M (toFlat s) ↔ Satisfies M s := by
  let ambient : Env (Sigma C) := fun _ => .unit
  change M.Satisfies (Program.ofCFGEntry s.1.admission.typed) (Program.ofCFGEntry s.2.admission.typed) ↔ _
  rw [satisfies_ofCFGEntry_iff _ _ _ ambient]
  exact forall_congr' fun x => by rw [← observe_entry s.1 M x ambient, ← observe_entry s.2 M x ambient]

theorem store_rename (I : Captures V β) (rename : V ≃ W) (record : Record) :
    (I.rename rename).store record = I.store record ∘ rename.symm := by
  funext key
  obtain ⟨name, rfl⟩ := rename.surjective key
  change NamedFlat.Entry.store (I.rename rename).names β record (some (rename name)) =
    NamedFlat.Entry.store I.names β record (some (rename.symm (rename name)))
  rw [rename.symm_apply_apply]
  unfold NamedFlat.Entry.store
  congr 2
  unfold NamedFlat.first
  congr 1
  funext i
  cases h : I.names i <;> simp [Captures.rename, h]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
