module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)
open Silmaril.MLIR.MemRef (Buffer)

private theorem ofFnM_get {α : Type} {count : Nat} {f : Fin count → Option α}
    {output : Vector α count} (success : Vector.ofFnM f = some output) (arrival : Fin count) :
    f arrival = some output[arrival.val] := by
  induction count with
  | zero => exact arrival.elim0
  | succ count ih =>
    rw [Vector.ofFnM_succ] at success
    obtain ⟨earlier, checked, next⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨last, selected, packed⟩ := Option.bind_eq_some_iff.mp next
    change some (earlier.push last) = some output at packed
    cases Option.some.inj packed
    refine Fin.lastCases ?_ (fun i => ?_) arrival
    · simpa only [Fin.val_last, Vector.getElem_push_eq] using selected
    · simpa only [Fin.val_castSucc, Vector.getElem_push_lt i.isLt] using ih checked i

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {store : PrefixStore args} {arm : Occurrence preds → Memory.Graph args}
variable {candidate : Candidate args preds} {input : Tuple (Val cells) args} {edited : Bank args preds}

theorem check_eq_some_iff :
    check preds store arm candidate input = some edited ↔
      ∀ arrival, rewriteArm store (arm arrival) (candidate arrival) input = some edited[arrival.val] := by
  constructor
  · exact fun success arrival => ofFnM_get success arrival
  · intro every
    unfold check
    rw [funext every]
    change Vector.ofFnM (fun arrival : Occurrence preds => pure edited[arrival.val]) = pure edited
    rw [Vector.ofFnM_pure, Vector.ofFn_getElem]

theorem check_eq_none_iff :
    check preds store arm candidate input = none ↔
      ∃ arrival, rewriteArm store (arm arrival) (candidate arrival) input = none := by
  constructor
  · intro refused
    by_contra allAccepted
    push Not at allAccepted
    let result := Vector.ofFn fun arrival =>
      (rewriteArm store (arm arrival) (candidate arrival) input).get
        (Option.isSome_iff_ne_none.mpr (allAccepted arrival))
    have success : check preds store arm candidate input = some result := check_eq_some_iff.mpr (fun arrival => by
      simp only [result, Vector.getElem_ofFn, Option.some_get])
    rw [refused] at success
    contradiction
  · rintro ⟨arrival, refused⟩
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro result success
    have accepted := check_eq_some_iff.mp success arrival
    rw [refused] at accepted
    contradiction

theorem check_memref_arm (success : check preds store arm candidate input = some edited)
    (arrival : Occurrence preds) (initial : Buffer cells) :
    observe edited[arrival.val] input initial = observe (store.prepend (arm arrival)) input initial := by
  have packet := (rewriteArm_observations input (check_eq_some_iff.mp success arrival) initial.cell).1
  rw [lower_run, lower_run]
  simp only [PrefixStore.prepend_denote, packet]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Proofs
