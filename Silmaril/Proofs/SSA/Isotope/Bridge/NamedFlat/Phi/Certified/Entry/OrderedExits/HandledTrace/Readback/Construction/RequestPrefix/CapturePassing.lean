module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture.Defs
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CapturePassing

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture
open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive region splitTransfer term)
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)
open Silmaril.Elgot.ITree (Tree diverge_bind ret_inj)
open Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry (graphList inferSlots packValue graphList_entry_tree graphList_tree)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)

universe u w
variable {F : Type} {E : Type w → Type w} {α : Type u} {blocks exits labels n : Nat}

private theorem transfer_run (instr : Primitive E F α) (decoders : Nat)
    (row : Flat F labels n) (env : Env α) (label : Fin labels) (arg : Tm Empty F n)
    (read : transferOperand decoders row = some (label, arg)) :
    region instr env row.erase = region instr env (.br label.val (erase arg)) := by
  induction decoders generalizing n env label with
  | zero =>
    cases row <;> cases read
    rfl
  | succ k ih =>
    cases row with
    | br _ _ | let₁ _ _ | case _ _ _ => cases read
    | let₂ pair rest =>
      simp only [transferOperand, Option.map_eq_some_iff] at read
      obtain ⟨⟨target, operand⟩, accepted, equal⟩ := read
      cases equal
      simp only [Flat.erase, region, erase, term, bind_assoc]
      apply bind_congr
      intro value
      cases value with
      | pair left right => exact ih rest (extend (extend env left) right) _ _ accepted
      | atom _ | inl _ | inr _ | unit => simp only [diverge_bind]

private theorem fold_decoders_run (instr : Primitive E F α) (decoders : Nat)
    (row : Flat F labels n) (env : Env α) :
    region instr env (foldDecoders decoders row).erase = region instr env row.erase := by
  unfold foldDecoders
  cases read : transferOperand decoders row with
  | none => rfl
  | some transfer =>
    obtain ⟨label, arg⟩ := transfer
    exact (transfer_run instr decoders row env label arg read).symm

theorem prepared_run (instr : Primitive E F α) (source : FiniteCFG F blocks exits n) (env : Env α) :
    region instr env (prepared source).erase = region instr env source.erase := by
  let slots := inferSlots source
  let carried := graphList source slots
  have steps (p : BlockInput α blocks) :
      region instr (extend env p.2) (foldDecoders slots.length (carried.block p.1)).erase =
        region instr (extend env p.2) (carried.block p.1).erase :=
    fold_decoders_run instr slots.length _ _
  have folded : region instr env (prepared source).erase = region instr env carried.erase := by
    change region instr env (.cfg carried.entry.erase blocks
      (fun i => (foldDecoders slots.length (carried.block i)).erase)) = _
    simp only [FiniteCFG.erase, region, steps]
  exact folded.trans (graphList_tree instr source slots env)

theorem seed_value {A : Type 1} {Events : Type → Type}
    {sig : PrimitiveSignature F} {context : BoundCtx PacketType n}
    {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
    {source : FiniteCFG F blocks exits n} (built : Compiled sig context packets outputs source)
    (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.checked.publicReadback.provenance.seed =
      packValue env (inferSlots source) (packetValue env built.seed) := by
  let prov := built.checked.publicReadback.provenance
  have seedTree : region instr env (graphList source (inferSlots source)).entry.erase =
      pure (prov.start.val, packetValue env prov.seed) := by
    change region instr env (prepared source).entry.erase = _
    rw [← built.checked.emitted.entry_eq, prov.sourceEntry, region, packet_term_tree, pure_bind]
  rw [graphList_entry_tree, built.entry_eq, region, packet_term_tree] at seedTree
  simp only [pure_bind, built.start.isLt, ↓reduceIte] at seedTree
  exact congrArg Prod.snd ((ret_inj (E := Events)).mp seedTree).symm

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.CapturePassing
