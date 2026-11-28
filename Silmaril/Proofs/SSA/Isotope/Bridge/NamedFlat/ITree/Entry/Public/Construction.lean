module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Construction

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback (Provenance packetTerm)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (FiniteCFG Region)

variable {V K : Type 1} [DecidableEq V] {F : Type}

theorem packetClosed (graph : CFG V K F)
    (closed : ∀ i : Fin graph.blocks.length, graph.blocks[i.val].2.body.toRegion.fv ⊆
      {graph.blocks[i.val].2.param}) : RoundTrip.PacketClosed graph := by
  intro item mem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
  exact closed ⟨i, hi⟩

theorem erase_eq {blocks publicBlocks exits publicExits publicCaptures : Nat}
    {flat : FiniteCFG F blocks exits 1} {publicCode : FiniteCFG F publicBlocks publicExits publicCaptures}
    (p : Provenance flat publicCode) (seed : p.seed = .var (0 : Fin 1)) (slot : p.slot.val = 0) :
    flat.erase = publicCode.erase := by
  have entry : flat.entry.erase = publicCode.entry.erase := by
    rw [p.sourceEntry, p.publicEntry, seed, slot]
    rfl
  have count := p.count
  subst publicBlocks
  exact congrArg₂ (fun entry rows => Region.cfg entry blocks rows) entry
    (funext fun i => (p.sourceRow i).trans (p.publicRow i).symm)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Construction
