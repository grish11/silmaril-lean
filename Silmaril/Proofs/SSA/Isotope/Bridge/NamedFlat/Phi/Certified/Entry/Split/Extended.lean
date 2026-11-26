module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Extended.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry (inputEnv)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Record (Input inputEnv_reindex)

universe u v

variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  {I : Captures V β} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

theorem packed_reindex (original : Admitted P I K D) (plan : Plan V W K J)
    (result : Generated plan original.source original.inputs I.names β D)
    (layout : ExtendedLayout plan I result.extra) (M : Model (κ := κ) Events P.Instr)
    (record : Input (extendedTypes β result.extra)) (ambient : Env (Sigma C)) :
    original.observePacked M (retainedRecord β result.extra record) ambient =
      (original.ofExtended plan result layout).observePacked M record ambient := by
  let store := layout.captures.store record ∘ plan.register
  have renamed : plan.renameStore store = layout.captures.store record := by
    funext key
    simp [store, Plan.renameStore, Function.comp_def]
  have agrees (i : Fin n) :
      inputEnv β (retainedRecord β result.extra record) i.val =
        captureEnv I.names store i.val :=
    (inputEnv_reindex (originalSlots β result.extra) record i).trans
      ((layout.captures.inputEnv_eq record ((originalSlots β result.extra).toFun i)).trans
        (by simpa only [renamed, ExtendedLayout.captures] using
          originalSlots_agree (plan := plan) (names := I.names) (β := β) result.extra store i))
  calc
    _ = PureCapture.sourceObservation M.raw original.source store :=
      (original.observe_toFlat_of_capture M _ ambient store agrees).symm
    _ = PureCapture.sourceObservation M.raw (plan.rewrite original.source) (plan.renameStore store) :=
      result.sourceObservation_eq M.raw store
    _ = _ := by
      rw [renamed]
      exact (original.ofExtended plan result layout).observe_toFlat M record ambient

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split
