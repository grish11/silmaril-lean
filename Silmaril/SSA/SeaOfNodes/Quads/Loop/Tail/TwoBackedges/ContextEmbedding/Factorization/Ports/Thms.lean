module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports

/-! Typed preimages and the exact image of the valuation reduct. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap PortMap reduct)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old new : List (ValueSort Width)} {t : SeaOfNodes.Diamond.Ty Width}
variable {S T : EntrySignature}

theorem preimage_sound (map : BankMap old new) (target : Port (dataPorts new) t)
    (source : Port (dataPorts old) t) (found : preimage map target = some source) :
    map t source = target :=
  Proofs.preimage_sound map target source found

theorem preimage_isSome (map : BankMap old new) (target : Port (dataPorts new) t) :
    (preimage map target).isSome ↔ ∃ source, map t source = target :=
  Proofs.preimage_isSome map target

theorem extendInput_unused (map : PortMap S T) (input : Valuation S) (fill : Valuation T)
    (target : Port (dataPorts T.regs) t) (unused : ¬ ∃ source, map t source = target) :
    (extendInput map input fill).get target = fill.get target :=
  Proofs.extendInput_unused map input fill target unused

theorem reduct_extendInput (map : PortMap S T) (input : Valuation S) (fill : Valuation T)
    (consistent : Consistent map input) : reduct map (extendInput map input fill) = input :=
  Proofs.reduct_extendInput map input fill consistent

theorem reduct_consistent (map : PortMap S T) (target : Valuation T) : Consistent map (reduct map target) :=
  Proofs.reduct_consistent map target

/-- A lift exists exactly for fibre-consistent inputs, with arbitrary values for unused ports. -/
theorem liftChecked_eq (map : PortMap S T) (input : Valuation S) (fill : Valuation T) (target : Valuation T) :
    liftChecked map input fill = some target ↔
      target = extendInput map input fill ∧ Consistent map input :=
  Proofs.liftChecked_eq map input fill target

theorem reduct_image_iff (map : PortMap S T) (input : Valuation S) :
    (∃ target, reduct map target = input) ↔ Consistent map input :=
  Proofs.reduct_image_iff map input

theorem liftChecked_isSome (map : PortMap S T) (input : Valuation S) (fill : Valuation T) :
    (liftChecked map input fill).isSome ↔ Consistent map input := by
  simp only [Option.isSome_iff_exists, liftChecked_eq]
  exact ⟨fun ⟨_, _, consistent⟩ => consistent, fun consistent => ⟨_, rfl, consistent⟩⟩

theorem liftChecked_none_iff (map : PortMap S T) (input : Valuation S) (fill : Valuation T) :
    liftChecked map input fill = none ↔ ¬ Consistent map input :=
  Option.not_isSome_iff_eq_none.symm.trans (not_congr (liftChecked_isSome map input fill))

theorem liftChecked_sound (map : PortMap S T) (input : Valuation S) (fill target : Valuation T)
    (accepted : liftChecked map input fill = some target) : reduct map target = input := by
  obtain ⟨rfl, consistent⟩ := (liftChecked_eq map input fill target).mp accepted
  exact reduct_extendInput map input fill consistent

theorem liftChecked_unused (map : PortMap S T) (input : Valuation S) (fill target : Valuation T)
    (accepted : liftChecked map input fill = some target) (port : Port (dataPorts T.regs) t)
    (unused : ¬ ∃ source, map t source = port) : target.get port = fill.get port := by
  obtain ⟨rfl, _⟩ := (liftChecked_eq map input fill target).mp accepted
  exact extendInput_unused map input fill port unused

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
