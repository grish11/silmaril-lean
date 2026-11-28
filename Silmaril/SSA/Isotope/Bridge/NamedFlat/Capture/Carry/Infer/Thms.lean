module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Support.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Closure

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry

open LambdaSSA (FiniteCFG)

universe u
variable {F : Type u} {blocks exits n : Nat}

/-- The inferred list includes exactly the caller fields read by some
written row. The block argument and local binders are excluded. -/
theorem mem_inferSlots (g : FiniteCFG F blocks exits n) (slot : Fin n) :
    slot ∈ inferSlots g ↔ ∃ i, UsesVar (g.block i) slot.succ.val :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.mem_inferSlots g slot

/-- Newest-first indices decrease along the inferred list. -/
theorem inferSlots_ordered (g : FiniteCFG F blocks exits n) :
    (inferSlots g).Pairwise (fun older newer => newer < older) :=
  (List.pairwise_reverse.mpr (List.pairwise_lt_finRange n)).filter _

/-- Carrying a layout introduces no ambient read and removes all the
selected slots from the free variables of the written rows. -/
theorem graphList_older {g : FiniteCFG F blocks exits n} {slots : List (Fin n)} {older : Fin n} {row : Fin blocks}
    (used : UsesVar ((graphList g slots).block row) older.succ.val) :
    UsesVar (g.block row) older.succ.val ∧ older ∉ slots :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graphList_older used

/-- Any shared layout covering the written reads gives packet-only rows. -/
theorem packetOnly_of_covers (g : FiniteCFG F blocks exits n) (slots : List (Fin n))
    (covers : ∀ row slot, UsesVar (g.block row) slot.succ.val → slot ∈ slots) (row : Fin blocks) :
    ((graphList g slots).block row).erase.Scoped (blocks + exits) 1 :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.packetOnly_of_covers g slots covers row

/-- Once the inferred fields are carried, each actual row is scoped with
the packet as its sole free value variable. Labels and local binders retain
their original scopes. -/
theorem infer_packetOnly (g : FiniteCFG F blocks exits n) (row : Fin blocks) :
    ((graphList g (inferSlots g)).block row).erase.Scoped (blocks + exits) 1 :=
  packetOnly_of_covers g _ (fun i slot used => (mem_inferSlots g slot).mpr ⟨i, used⟩) row

end Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
