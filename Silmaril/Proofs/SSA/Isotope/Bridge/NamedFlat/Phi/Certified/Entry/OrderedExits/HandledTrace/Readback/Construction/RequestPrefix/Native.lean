module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Native.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Execution

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Native

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Native (Compiled)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive region splitTransfer)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)
open Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed
  (schedule_cases_run)

universe u w
variable {F : Type} {Events : Type w → Type w} {A : Type u} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
  {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

theorem preserves_run (built : Compiled sig context packets outputs source)
    (instr : Primitive Events F A) (env : Env A) :
    region instr env source.erase = region instr env built.code.erase := by
  obtain ⟨decideEq, accepted⟩ := built.entry_eq
  let _ : DecidableEq F := decideEq
  have entry := schedule_cases_run instr env _ _ _ accepted
  have steps : (fun p : BlockInput A blocks =>
      region instr (extend env p.2) (source.block p.1).erase >>= fun out => pure (splitTransfer blocks out)) =
      (fun p : BlockInput A blocks =>
        region instr (extend env p.2) (built.code.block p.1).erase >>= fun out => pure (splitTransfer blocks out)) := by
    funext p
    obtain ⟨decideRow, checked⟩ := built.row_eq p.1
    let _ : DecidableEq F := decideRow
    rw [schedule_cases_run instr (extend env p.2) _ _ _ checked]
  simp only [FiniteCFG.erase, region, entry, steps]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Native
