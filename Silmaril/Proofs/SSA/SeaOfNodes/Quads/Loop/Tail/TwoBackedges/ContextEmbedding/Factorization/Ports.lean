module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! The checked lift recognizes exactly the image of the valuation reduct. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Proofs

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.SCCP (decideTupleCovers)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Identification (BankMap PortMap ports reduct reduct_get)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old new : List (ValueSort Width)} {t : SeaOfNodes.Diamond.Ty Width}
variable {S T : EntrySignature}

private theorem preimageCandidate_sound (map : BankMap old new) (target : Port (dataPorts new) t)
    (candidate : Sigma (Port (dataPorts old))) (source : Port (dataPorts old) t)
    (found : preimageCandidate map target candidate = some source) : map t source = target := by
  by_cases same : slot (map candidate.1 candidate.2) = slot target
  · obtain ⟨s, port⟩ := candidate
    obtain ⟨rfl, image⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ same)
    have eqPort : port = source := by simpa [preimageCandidate, same] using found
    exact eqPort ▸ eq_of_heq image
  · simp [preimageCandidate, same] at found

theorem preimage_sound (map : BankMap old new) (target : Port (dataPorts new) t)
    (source : Port (dataPorts old) t) (found : preimage map target = some source) : map t source = target := by
  obtain ⟨_, candidate, _, _, hit, _⟩ := List.findSome?_eq_some_iff.mp found
  exact preimageCandidate_sound map target candidate source hit

theorem preimage_isSome (map : BankMap old new) (target : Port (dataPorts new) t) :
    (preimage map target).isSome ↔ ∃ source, map t source = target := by
  constructor
  · cases h : preimage map target with
    | none => simp
    | some source => exact fun _ => ⟨source, preimage_sound map target source h⟩
  · rintro ⟨source, rfl⟩
    apply List.findSome?_isSome_iff.mpr
    exact ⟨⟨t, source⟩, Identification.ports_complete source, by simp [preimageCandidate]⟩

theorem extendInput_unused (map : PortMap S T) (input : Valuation S) (fill : Valuation T)
    (target : Port (dataPorts T.regs) t) (unused : ¬ ∃ source, map t source = target) :
    (extendInput map input fill).get target = fill.get target := by
  have miss : preimage map target = none := by
    cases found : preimage map target with
    | none => rfl
    | some source => exact False.elim (unused ⟨source, preimage_sound map _ _ found⟩)
  rw [extendInput, get_tabulate, miss]

private theorem valuation_eq {left right : Valuation S}
    (reads : ∀ {s} (p : Port (dataPorts S.regs) s), left.get p = right.get p) : left = right :=
  (tabulate_get_eq left).symm.trans
    ((congrArg (tabulate _) (funext fun _ => funext reads)).trans (tabulate_get_eq right))

theorem reduct_extendInput (map : PortMap S T) (input : Valuation S) (fill : Valuation T)
    (consistent : Consistent map input) : reduct map (extendInput map input fill) = input := by
  have reads {s} (port : Port (dataPorts S.regs) s) :
      (reduct map (extendInput map input fill)).get port = input.get port := by
    rw [reduct_get, extendInput, get_tabulate]
    cases found : preimage map (map s port) with
    | none =>
      have hit := (preimage_isSome map (map s port)).mpr ⟨port, rfl⟩
      simp [found] at hit
    | some representative =>
      exact consistent s representative port (preimage_sound map _ _ found)
  exact valuation_eq reads

theorem reduct_consistent (map : PortMap S T) (target : Valuation T) : Consistent map (reduct map target) := by
  intro sort left right shared
  rw [reduct_get, reduct_get, shared]

private def zeroFill : (regs : List (ValueSort Width)) → Tuple (Val Word) (dataPorts regs)
  | [] => .nil
  | .predicate :: rest => .cons ⟨false⟩ (zeroFill rest)
  | .data width :: rest => .cons (0 : Word width) (zeroFill rest)

theorem reduct_image_iff (map : PortMap S T) (input : Valuation S) :
    (∃ target, reduct map target = input) ↔ Consistent map input :=
  ⟨fun ⟨target, eq⟩ => eq ▸ reduct_consistent map target,
    fun h => ⟨extendInput map input (zeroFill T.regs), reduct_extendInput map input (zeroFill T.regs) h⟩⟩

private theorem exactFacts_iff (input reduced : Valuation S) :
    TupleCovers (tabulate (dataPorts S.regs) (F := SeaOfNodes.Diamond.SCCP.Fact Word)
      fun p => .constant (input.get p)) reduced ↔ reduced = input := by
  constructor
  · intro covers
    have reads {s} (port : Port (dataPorts S.regs) s) : reduced.get port = input.get port := by
      have atPort := covers port
      rw [get_tabulate] at atPort
      exact Eq.symm atPort
    exact valuation_eq reads
  · rintro rfl sort port
    rw [get_tabulate]
    rfl

theorem liftChecked_eq (map : PortMap S T) (input : Valuation S) (fill : Valuation T) (target : Valuation T) :
    liftChecked map input fill = some target ↔
      target = extendInput map input fill ∧ Consistent map input := by
  let candidate := extendInput map input fill
  let facts : EntryFacts S.regs := tabulate (dataPorts S.regs) fun p => .constant (input.get p)
  let coverage := @decideTupleCovers _ _ _ S.bankEq facts (reduct map candidate)
  change ((if @decide _ coverage then some candidate else none) = some target) ↔ _
  have check : @decide _ coverage = true ↔ reduct map candidate = input :=
    ⟨fun h => (exactFacts_iff input _).mp (@of_decide_eq_true _ coverage h),
      fun h => @decide_eq_true _ coverage ((exactFacts_iff input _).mpr h)⟩
  constructor
  · split
    · rename_i accepted
      intro lifted
      exact ⟨(Option.some.inj lifted).symm, (check.mp accepted) ▸ reduct_consistent map _⟩
    · simp
  · rintro ⟨rfl, consistent⟩
    rw [ite_eq_left (check.mpr (reduct_extendInput map input fill consistent))]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Proofs
