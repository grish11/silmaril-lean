module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Proofs

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate cell)
open Entry.Composition.Retained.Load.Static (AddressContract)
open LoadTail.PrefixWord.Sequence.Replay.Search (inferCandidate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {input oldInput : Tuple (Val cells) args} {stage : MixedTail.Result cells args preds}
variable {conflict : Alias cells args preds} {report : Refusal cells args preds}
variable {entry : Memory.Graph args} {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args}
variable {suffix : Memory.Graph (.word :: args)} {source : Program cells args preds}
variable {requests : List Replay.Request} {original : Replay.Result cells args preds}

private theorem mem_obligations {site : Site preds} {port : Port args .address} :
    (site, port) ∈ obligations stage ↔ site.portAt stage = some port := by
  cases site <;>
    simp [obligations, Site.portAt, List.mem_flatMap, List.mem_map, Prod.exists, List.mk_mem_zipIdx_iff_getElem?]

private theorem valid_iff_obligations : (contractOf stage).Valid input ↔
    ∀ pair ∈ obligations stage, cell input stage.emission.edit.address ≠ cell input pair.2 := by
  simp only [contractOf, Contract.Valid, AddressContract.Valid, MixedTail.Result.facts, Certificate.Valid,
    Vector.getElem_ofFn, List.not_mem_nil, false_implies, implies_true, and_true]
  constructor
  · rintro ⟨entry, arms⟩ ⟨site, port⟩ member
    have found := mem_obligations.mp member
    cases site with
    | entry index => exact entry port (List.mem_of_getElem? found)
    | arm occurrence index => exact arms occurrence port (List.mem_of_getElem? found)
  · intro valid
    constructor
    · intro port member
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      exact valid (.entry index, port) (mem_obligations.mpr found)
    · intro occurrence port member
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      exact valid (.arm occurrence index, port) (mem_obligations.mpr found)

theorem alias_none_iff : alias? stage input = none ↔ (contractOf stage).Valid input := by
  rw [valid_iff_obligations]
  simp [alias?, List.find?_eq_none]

theorem alias_sound (found : alias? stage input = some conflict) : conflict.Valid stage input := by
  unfold alias? at found
  obtain ⟨⟨site, port⟩, selected, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  have equal := List.find?_some selected
  change decide (cell input stage.emission.edit.address = cell input port) = true at equal
  exact ⟨mem_obligations.mp (List.mem_of_find?_eq_some selected), rfl, (of_decide_eq_true equal).symm⟩

private theorem from_pending (recorded : Replay.Trace fits arm suffix oldInput entry source requests original)
    {rest : List (MixedTail.Result cells args preds)}
    (pending : (lowerFrom input original.admitted entry source).pending = stage :: rest) :
    let checkedPrefix := lowerFrom input original.admitted entry source
    MixedTail.lower fits arm suffix oldInput checkedPrefix.replay.retained = some stage ∧
      stage.emission.programs.original = checkedPrefix.replay.programs.optimized ∧ reuse stage input = none := by
  induction recorded with
  | done | refused => cases pending
  | @step entry source _ _ first _ accepted sourceEq _ _ _ ih =>
    simp only [Replay.Result.prepend, lowerFrom] at pending ⊢
    cases checked : reuse first input with
    | none =>
      simp only [checked, Chain.Result.stop] at pending
      have same := (List.cons.inj pending).1
      subst stage
      simpa only [checked, Chain.Result.stop, Replay.Result.stop] using
        And.intro (Replay.check_accepted accepted).1 (And.intro sourceEq checked)
    | some rebound =>
      obtain ⟨_, rfl⟩ := reuse_eq_some_iff.mp checked
      simp only [checked, Chain.Result.prepend, Replay.Result.prepend] at pending ⊢
      exact ih pending

private theorem pending_admitted
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original)
    {rest : List (MixedTail.Result cells args preds)}
    (pending : (Chain.lower original entry input).pending = stage :: rest) :
    let checkedPrefix := Chain.lower original entry input
    MixedTail.lower fits arm suffix oldInput checkedPrefix.replay.retained = some stage ∧
      stage.emission.programs.original = checkedPrefix.replay.programs.optimized ∧ reuse stage input = none := by
  have sourceEq : original.programs.original = lowerBank preds fits cells (some entry) arm suffix := by
    cases recorded <;> rfl
  unfold Chain.lower at pending ⊢
  rw [sourceEq] at pending ⊢
  exact from_pending recorded pending

theorem lower_none_iff
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    (lower original entry input).refusal = none ↔ (Chain.lower original entry input).pending = [] := by
  obtain ⟨saved, _, _, _⟩ := Chain.lower_accounting (input := input) recorded
  cases pending : (Chain.lower original entry input).pending with
  | nil => simp [lower, explain, pending]
  | cons stage rest =>
    have rejected := (pending_admitted recorded pending).2.2
    cases found : alias? stage input with
    | none => exact False.elim ((reuse_eq_none_iff.mp rejected) (alias_none_iff.mp found))
    | some conflict => simp [lower, explain, pending, saved, found]

theorem lower_refusal
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (explained : (lower original entry input).refusal = some report) :
    let checkedPrefix := (lower original entry input).checkedPrefix
    ∃ stage rest, checkedPrefix.pending = stage :: rest ∧
      original.admitted.drop report.stageIndex = stage :: rest ∧
      report.stageIndex = checkedPrefix.replay.deleted ∧ report.version = stage.version ∧
      report.store = stage.emission.edit.address ∧
      stage.emission.programs.original = checkedPrefix.replay.programs.optimized ∧
      inferCut report.version checkedPrefix.replay.retained = some (stage.emission.edit, stage.ports) ∧
      inferCandidate preds report.store arm = some stage.candidate ∧
      reuse stage input = none ∧ report.conflict.Valid stage input := by
  obtain ⟨saved, _, _, unaccepted⟩ := Chain.lower_accounting (input := input) recorded
  cases pending : (Chain.lower original entry input).pending with
  | nil => simp [lower, explain, pending] at explained
  | cons stage rest =>
    obtain ⟨accepted, sourceEq, rejected⟩ := pending_admitted recorded pending
    obtain ⟨_, cut, _, arms, _, _⟩ := MixedTail.lower_checked accepted
    simp only [lower, explain, pending, List.head?_cons, saved, Option.pure_def] at explained
    change (alias? stage input >>= fun conflict =>
      some ⟨(Chain.lower original entry input).replay.deleted, stage.version, stage.emission.edit.address, conflict⟩)
      = some report at explained
    obtain ⟨conflict, found, same⟩ := Option.bind_eq_some_iff.mp explained
    cases Option.some.inj same
    exact ⟨stage, rest, pending, unaccepted.symm.trans pending, rfl, rfl, rfl, sourceEq, cut, arms, rejected,
      alias_sound found⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Proofs
