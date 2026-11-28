module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Defs
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region splitTransfer)
open Silmaril.Elgot (iter liftPure mapReturn LawfulElgotMonad)

universe u v w
variable {Events : Type w → Type w} {F : Type v} {α β : Type u}
  {blocks publicBlocks exits publicExits captures publicCaptures : Nat}
  {source : FiniteCFG F blocks exits captures} {target : FiniteCFG F publicBlocks publicExits publicCaptures}
  {left : Primitive Events F α} {right : Primitive Events F β}
  {leftEnv : Env α} {rightEnv : Env β} {atom : α → β}

private theorem flatRun (instr : Primitive Events F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) :
    region instr env graph.erase =
      transfer instr env blocks graph.entry >>= Sum.elim pure (iter (blockStep instr graph env)) := by
  have stepEq : blockStep instr graph env = fun p =>
      region instr (extend env p.2) (graph.block p.1).erase >>= fun out => pure (splitTransfer blocks out) := by
    funext p
    unfold blockStep transfer
    rw [map_eq_pure_bind]
  rw [stepEq]
  simp only [FiniteCFG.erase, region, transfer, ← bind_pure_comp, bind_assoc, pure_bind]
  rfl

theorem execute (align : Alignment source target left right leftEnv rightEnv atom) :
    resultCodec atom <$> region left leftEnv source.erase = region right rightEnv target.erase := by
  let runLeft := blockStep left source leftEnv
  let runRight := blockStep right target rightEnv
  let project := resultCodec atom
  let observed := mapReturn runLeft (fun result => pure (project result))
  have square : (observed >=> liftPure (Sum.map id align.state)) = (liftPure align.state >=> runRight) := by
    funext pending
    change (observed pending >>= liftPure (Sum.map id align.state)) = (pure (align.state pending) >>= runRight)
    have step := align.step pending
    change _ <$> runLeft pending = runRight (align.state pending) at step
    rw [pure_bind, ← step, ← bind_pure_comp]
    simp only [observed, mapReturn, bind_assoc]
    congr 1
    funext result
    cases result <;> simp [liftPure, project]
  have loopEq pending : project <$> iter runLeft pending = iter runRight (align.state pending) := by
    have natural := congrFun (LawfulElgotMonad.naturality runLeft (fun x => pure (project x))) pending
    have uniform := congrFun (LawfulElgotMonad.uniformity observed runRight align.state square) pending
    have commutes := natural.trans uniform
    change (iter runLeft pending >>= fun x => pure (project x)) =
      (pure (align.state pending) >>= iter runRight) at commutes
    simpa only [map_eq_pure_bind, pure_bind] using commutes
  let startLeft := transfer left leftEnv blocks source.entry
  let startRight := transfer right rightEnv publicBlocks target.entry
  let resumeLeft := Sum.elim pure (iter runLeft)
  let resumeRight := Sum.elim pure (iter runRight)
  change resultCodec atom <$> region left leftEnv source.erase = region right rightEnv target.erase
  rw [flatRun, flatRun, map_bind]
  change (startLeft >>= fun out => project <$> resumeLeft out) = startRight >>= resumeRight
  calc
    _ = startLeft >>= (resumeRight ∘ Sum.map project align.state) := by
      apply bind_congr
      intro pending
      cases pending with
      | inl result => exact map_pure _ _
      | inr state => exact loopEq state
    _ = (Sum.map project align.state <$> startLeft) >>= resumeRight := by
      simp only [← bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    _ = _ := congrArg (· >>= resumeRight) align.entry

private theorem valueCodec_tag (atom : α → β) (index : Nat) (value : Value α) :
    valueCodec atom (Region.packedExitValue index value) = Region.packedExitValue index (valueCodec atom value) := by
  induction index <;> simp_all only [Region.packedExitValue, valueCodec]

theorem packed (align : Alignment source target left right leftEnv rightEnv atom) :
    resultCodec atom <$> (region left leftEnv source.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (region right rightEnv target.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) := by
  rw [← execute align]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext out
  simp only [resultCodec, FiniteCFG.packedTreeOutput, valueCodec_tag]

section Public

open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom Denote PacketType PrimitiveSignature Program)
open NamedFlat.Entry.Record (Input)

variable {κ V Reg K : Type 1} [DecidableEq V] [DecidableEq Reg] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{0, 0} κ}
  {I : NamedFlat.Entry.Interface κ Reg (Option K)} {fields : Option K → List (Reg × Ty κ)}
  {C : Captures V I.context} {signature : PrimitiveSignature P.Instr}
  {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {program : Program signature inputs outputs} {input : Fin a}

local notation "Atoms" => AtomValues.carrier (κ := κ)

theorem observation (source : Admission P I fields C)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields source.code)
    (recompiled : NamedFlat.Entry.LiveOut.Admission P I fields lowered.source)
    (M : Model (κ := κ) (Event signature.Request signature.Reply) P.Instr)
    (record : Input I.context) (atom : Sigma Atoms → Atom) (entry : Program.PackedEntry program input)
    (publicAmbient publicRecord : Env Atom) (ambient : Env (Sigma Atoms))
    (align : Alignment source.code entry.target M.raw signature.primitive
      (NamedFlat.Entry.inputEnv I.context record) publicRecord atom) :
    resultCodec atom <$> region M.raw (extend ambient (encodeValue Atoms _ record)) recompiled.program.code =
      entry.observe publicAmbient publicRecord := by
  let decoded := NamedFlat.Entry.inputEnv I.context record
  have leftPacked := NamedFlat.Capture.packed_context_tree M.raw source.typed ambient decoded
  have rightPacked := let _ := signature.typing
    NamedFlat.Capture.packed_context_tree signature.primitive entry.typed publicAmbient publicRecord
  have unpackInput := congrArg (fun arg => region M.raw (extend ambient arg)
    (LambdaSSA.Semantics.Interaction.Typed.Ordered.Program.ofCFGEntry source.typed).code)
    (NamedFlat.Entry.inputEnv_packet I.context record).symm
  exact (congrArg (Functor.map (resultCodec atom))
    ((lowered.packed_roundTrip M source.typed recompiled record ambient).symm.trans
      (unpackInput.trans leftPacked))).trans ((packed align).trans rightPacked.symm)

end Public

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
