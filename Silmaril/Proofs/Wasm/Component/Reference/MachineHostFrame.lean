module

public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Machine.HostFrame
open Silmaril.Wasm.Execution.Core

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)}

private theorem finish_replace (cfg : Config E Host) (other : Host) (result : Ret E)
    (rest : List (Activation E Host)) :
    hostFinish result rest (replace cfg other) = replace (hostFinish result rest cfg) other := by
  have calls : lastCall? (replace cfg other) = lastCall? cfg := rfl
  cases rest <;> cases result <;> cases found : lastCall? cfg <;>
    simp only [hostFinish, calls, found] <;> rfl

private theorem observe_replace (cfg : Config E Host) (other : Host) (obs : HostObs) :
    observe (replace cfg other) obs = replace (observe cfg obs) other := by cases obs <;> rfl

private theorem fault_replace {cfg : Config E Host} {reason : String} (other : Host) (failed : Fault cfg reason) :
    Fault (replace cfg other) reason := by
  cases failed with
  | blockNoThread focused => exact .blockNoThread focused
  | switchMissing focused missing => exact .switchMissing focused missing
  | resumeMissing focused missing => exact .resumeMissing focused missing
  | calloutBadRet focused bad => exact .calloutBadRet focused bad

theorem step {before after : Config E Host} {label : Label E Host} (other : Host)
    (run : Step profile ready dispatch before label after) :
    (∃ host, Step profile ready dispatch (replace before other) label (replace after host)) ∨
    (∃ alternate, Step profile ready dispatch (replace before other) label alternate ∧
      ReadCut before other label after alternate) := by
  cases run with
  | popProg focused => exact .inl ⟨other, .popProg focused⟩
  | popCore focused => exact .inl ⟨other, .popCore focused⟩
  | threadExit focused => exact .inl ⟨other, .threadExit focused⟩
  | hostDone focused => exact .inl ⟨other, finish_replace .. ▸ .hostDone focused⟩
  | call focused => exact .inl ⟨other, .call focused⟩
  | callCore focused => exact .inl ⟨other, .callCore focused⟩
  | coreInternal focused status inner => exact .inl ⟨other, .coreInternal focused status inner⟩
  | coreReturned focused status => exact .inl ⟨other, .coreReturned focused status⟩
  | coreTrap focused status => exact .inl ⟨other, .coreTrap focused status⟩
  | coreCallout focused status => exact .inl ⟨other, .coreCallout focused status⟩
  | get focused => exact .inl ⟨other, .get focused⟩
  | modify focused => exact .inl ⟨other, .modify focused⟩
  | trap focused => exact .inl ⟨other, .trap focused⟩
  | choose answer focused allowed => exact .inl ⟨other, .choose answer focused allowed⟩
  | currentThread focused => exact .inl ⟨other, .currentThread focused⟩
  | newThread focused allocated => exact .inl ⟨other, .newThread focused allocated⟩
  | block focused => exact .inl ⟨other, .block focused⟩
  | blockSwitch focused found => exact .inl ⟨other, .blockSwitch focused found⟩
  | resumeThread focused found => exact .inl ⟨other, .resumeThread focused found⟩
  | @hostGet thread next frames rest focused =>
    classical
    by_cases same : next before.host = next other
    · refine .inl ⟨other, ?_⟩
      rw [show replace { before with ctl := ⟨thread, .prog (next before.host), frames⟩ :: rest } other =
        { replace before other with ctl := ⟨thread, .prog (next other), frames⟩ :: rest } by rw [same]; rfl]
      exact .hostGet focused
    · exact .inr ⟨_, .hostGet focused, .mk focused same⟩
  | @hostSet _ state _ _ _ focused => exact .inl ⟨state, .hostSet focused⟩
  | @emit thread obs next frames rest focused =>
    refine .inl ⟨other, ?_⟩
    have replaced := Step.emit (prof := profile) (hr := ready) (dispatch := dispatch)
      (m := replace before other) focused
    rw [observe_replace] at replaced
    exact replaced
  | fault failed => exact .inl ⟨other, .fault (fault_replace other failed)⟩
  | hostInvoke enabled fresh => exact .inl ⟨other, .hostInvoke enabled fresh⟩
  | hostTick enabled => exact .inl ⟨other, .hostTick enabled⟩
  | hostCancel enabled pending unresolved => exact .inl ⟨other, .hostCancel enabled pending unresolved⟩
  | hostRun enabled => exact .inl ⟨other, .hostRun enabled⟩

theorem steps {before after : Config E Host} {labels : List (Label E Host)} (other : Host)
    (run : Steps profile ready dispatch before labels after) :
    (∃ host, Steps profile ready dispatch (replace before other) labels (replace after host)) ∨
    (∃ leading label trailing reached reachedHost next alternate,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch before leading reached ∧
      Steps profile ready dispatch (replace before other) leading (replace reached reachedHost) ∧
      ReadCut reached reachedHost label next alternate ∧
      Step profile ready dispatch reached label next ∧
      Step profile ready dispatch (replace reached reachedHost) label alternate ∧
      Steps profile ready dispatch next trailing after) := by
  induction run generalizing other with
  | refl => exact .inl ⟨other, .refl _⟩
  | cons head tail ih =>
    rcases step other head with ⟨nextHost, pairedHead⟩ | ⟨_, pairedHead, cut⟩
    · rcases ih nextHost with ⟨host, pairedTail⟩ |
        ⟨leading, _, _, _, _, _, _, split, lhs, rhs, boundary, leftRead, rightRead, rest⟩
      · exact .inl ⟨host, .cons pairedHead pairedTail⟩
      · exact .inr ⟨_ :: leading, _, _, _, _, _, _, congrArg (List.cons _) split,
          .cons head lhs, .cons pairedHead rhs, boundary, leftRead, rightRead, rest⟩
    · exact .inr ⟨[], _, _, _, other, _, _, rfl, .refl _, .refl _, cut, head, pairedHead, tail⟩

variable {changes : ReturnFrame.Substitutions E Host}

local notation "PairedOf" => HostFrame.Related.Paired
local notation "BoundaryOf" => HostFrame.Related.Boundary

private theorem return_focus
    {left right leftNext rightNext : Config E Host} {label : Label E Host}
    (returned : ReturnFrame.Related.Returned changes left right label leftNext rightNext) :
    ∃ thread value frames rest, left.ctl = ⟨thread, .prog (.pure value), frames⟩ :: rest := by
  cases returned with
  | mk _ popping _ => exact ⟨_, _, _, _, popping⟩

private theorem read_not_return
    {left right leftNext rightNext alternate : Config E Host} {label : Label E Host}
    (cut : ReadCut left right.host label leftNext alternate)
    (returned : ReturnFrame.Related.Returned changes (replace left right.host) right label alternate rightNext) :
    False := by
  cases cut with
  | mk reading _ =>
    obtain ⟨_, _, _, _, popping⟩ := return_focus returned
    rw [show (replace left right.host).ctl = left.ctl from rfl, reading] at popping
    cases popping

private theorem return_host
    {left right leftNext rightNext : Config E Host} {label : Label E Host}
    (returned : ReturnFrame.Related.Returned changes left right label leftNext rightNext) :
    leftNext.host = left.host := by
  cases returned
  rfl

theorem paired_step
    {left right next : Config E Host} {label : Label E Host}
    (paired : PairedOf changes left right) (run : Step profile ready dispatch left label next) :
    ∃ next', Step profile ready dispatch right label next' ∧
      (PairedOf changes next next' ∨ BoundaryOf changes left right label next next') := by
  rcases step right.host run with ⟨other, replay⟩ | ⟨alternate, replay, cut⟩
  · rcases ReturnFrame.Related.step paired replay with ⟨next', run', aligned⟩ | ⟨next', run', returned⟩
    · have equal : other = next'.host := aligned.data.2.1
      rw [equal] at aligned
      exact ⟨next', run', .inl aligned⟩
    · have equal : other = right.host := return_host returned
      rw [equal] at returned
      exact ⟨next', run', .inr (.returned returned)⟩
  · rcases ReturnFrame.Related.step paired replay with ⟨next', run', aligned⟩ | ⟨_, _, returned⟩
    · exact ⟨next', run', .inr (.read cut aligned)⟩
    · exact (read_not_return cut returned).elim

theorem paired_steps
    {left right next : Config E Host} {labels : List (Label E Host)}
    (paired : PairedOf changes left right) (run : Steps profile ready dispatch left labels next) :
    (∃ next', Steps profile ready dispatch right labels next' ∧ PairedOf changes next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch left leading atLeft ∧
      Steps profile ready dispatch right leading atRight ∧ PairedOf changes atLeft atRight ∧
      BoundaryOf changes atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      Steps profile ready dispatch afterLeft trailing next) := by
  induction run generalizing right with
  | refl => exact .inl ⟨right, .refl _, paired⟩
  | cons head tail ih =>
    obtain ⟨_, replay, aligned | boundary⟩ := paired_step paired head
    · rcases ih aligned with ⟨_, replayTail, pairedTail⟩ |
        ⟨leading, _, _, _, _, _, _, split, lhs, rhs, reached, cut, leftStep, rightStep, rest⟩
      · exact .inl ⟨_, .cons replay replayTail, pairedTail⟩
      · exact .inr ⟨_ :: leading, _, _, _, _, _, _, congrArg (List.cons _) split,
          .cons head lhs, .cons replay rhs, reached, cut, leftStep, rightStep, rest⟩
    · exact .inr ⟨[], _, _, _, _, _, _, rfl, .refl _, .refl _, paired, boundary, head, replay, tail⟩

private theorem pairedUpdateGrows {grow : SingleThreaded.GrowOracle}
    {changes : ReturnFrame.Substitutions (core3 grow) Host}
    {left right : Config (core3 grow) Host}
    (paired : PairedOf changes left right) (growth : CoreUpdateGrows left) : CoreUpdateGrows right := by
  have lengths {before after : Config (core3 grow) Host}
      (framed : ReturnFrame.Related.Paired changes before after) :
      before.ctl.length = after.ctl.length := by
    cases framed with
    | mk controls _ => exact controls.length_eq
  rcases active : left.ctl with _ | ⟨⟨thread, focus, frames⟩, rest⟩
  · have size := lengths (before := replace left right.host) paired
    change left.ctl.length = right.ctl.length at size
    have empty : right.ctl = [] := List.length_eq_zero_iff.mp (by simpa only [active, List.length_nil] using size.symm)
    simp only [CoreUpdateGrows, empty]
  · have atReplaced : (replace left right.host).ctl = ⟨thread, focus, frames⟩ :: rest := active
    obtain ⟨_, _, matched, _⟩ := ReturnFrame.Related.Paired.retarget paired atReplaced focus right.host
    have sameStore : left.store = right.store := (ReturnFrame.Related.Paired.data paired).1
    rw [CoreUpdateGrows, active] at growth
    rw [CoreUpdateGrows, matched, ← sameStore]
    cases focus with
    | core _ _ => trivial
    | prog program =>
      cases program with
      | pure _ => trivial
      | op operation _ => cases operation <;> exact growth

theorem paired_growing_steps {grow : SingleThreaded.GrowOracle}
    {ready : HostReady Host} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {changes : ReturnFrame.Substitutions (core3 grow) Host}
    {left right next : Config (core3 grow) Host} {labels : List (Label (core3 grow) Host)}
    (paired : PairedOf changes left right) (run : CoreGrowthSteps profile ready dispatch left labels next) :
    (∃ next', CoreGrowthSteps profile ready dispatch right labels next' ∧ PairedOf changes next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      CoreGrowthSteps profile ready dispatch left leading atLeft ∧
      CoreGrowthSteps profile ready dispatch right leading atRight ∧ PairedOf changes atLeft atRight ∧
      BoundaryOf changes atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      CoreGrowthSteps profile ready dispatch afterLeft trailing next) := by
  induction run generalizing right with
  | refl => exact .inl ⟨right, .refl _, paired⟩
  | cons growth head tail ih =>
    have otherGrowth := pairedUpdateGrows paired growth
    obtain ⟨_, replay, aligned | boundary⟩ := paired_step paired head
    · rcases ih aligned with ⟨_, replayTail, pairedTail⟩ |
        ⟨leading, _, _, _, _, _, _, split, lhs, rhs, reached, cut, leftStep, rightStep, rest⟩
      · exact .inl ⟨_, .cons otherGrowth replay replayTail, pairedTail⟩
      · exact .inr ⟨_ :: leading, _, _, _, _, _, _, congrArg (List.cons _) split,
          .cons growth head lhs, .cons otherGrowth replay rhs, reached, cut, leftStep, rightStep, rest⟩
    · exact .inr ⟨[], _, _, _, _, _, _, rfl, .refl _, .refl _, paired, boundary, head, replay, tail⟩

theorem interior_step {grow : SingleThreaded.GrowOracle}
    {ready : HostReady Host} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {changes : ReturnFrame.Substitutions (core3 grow) Host}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) Host → Prop}
    (covers : ∀ first second, changes first second → protectedReturn first)
    {left right next : Config (core3 grow) Host} {label : Label (core3 grow) Host}
    (paired : PairedOf changes left right) (interior : InteriorFor protectedReturn left)
    (grows : CoreUpdateGrows left) (run : Step profile ready dispatch left label next) :
    ∃ other, CoreGrowthSteps profile ready dispatch right [label] other ∧ PairedOf changes next other := by
  obtain ⟨other, replay, aligned | boundary⟩ := paired_step paired run
  · exact ⟨other, .cons (pairedUpdateGrows paired grows) replay (.refl _), aligned⟩
  cases boundary with
  | read cut _ =>
    have notRead {cfg : Config (core3 grow) Host} {result alt : Config (core3 grow) Host}
        {lbl : Label (core3 grow) Host} {host : Host} (inside : InteriorFor protectedReturn cfg)
        (readCut : ReadCut cfg host lbl result alt) : False := by
      cases readCut with
      | mk focus _ => exact inside.1 _ _ _ _ focus
    exact (notRead interior cut).elim
  | returned popped =>
    obtain ⟨resume, _, thread, value, frames, rest, edge, reached⟩ := popped.left_input
    exact (interior.2 resume (covers resume _ edge) thread value frames rest reached).elim

theorem instCandidates_eq (store : CStore E) (inst : InstId) (left right : Nat → Bool)
    (agree : ∀ entry, store.inst? inst = some entry → ∀ thread ∈ entry.threads.elements,
      ∀ suspended, store.thread? thread = some suspended → suspended.blocked = true →
        ∀ query, suspended.readyCond = some (.host query) → left query = right query) :
    store.instCandidates left inst = store.instCandidates right inst := by
  unfold CStore.instCandidates
  split
  · rename_i entry live
    apply List.filter_congr
    intro thread member
    simp only [CStore.threadReady, CStore.threadIs]
    split
    · rename_i suspended found
      unfold Thread.ready
      cases blocked : suspended.blocked
      · rfl
      cases condition : suspended.readyCond with
      | none => rfl
      | some predicate =>
        cases predicate <;> try rfl
        rename_i query
        simp only [ReadyCond.eval, agree entry live thread member suspended found blocked query condition]
    · rfl
  · rfl

theorem sync_readiness {first second : ReturnFrame.Continuation E Host} {cfg other : Config E Host}
    (paired : Paired first second cfg other) (task : TaskId) {entry : Task E}
    (found : ArenaField.tasks.get? cfg.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : cfg.store.instCandidates (ready cfg.host) entry.inst = cfg.store.instCandidates (ready other.host) entry.inst)
    {thread frames rest} (focused : cfg.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest) :
    ∃ next next', Steps profile ready dispatch cfg [.tau, .tau, .tau] next ∧
      Steps profile ready dispatch other [.tau, .tau, .tau] next' ∧ Paired first second next next' := by
  let chooseNext : List ThreadId → P E Host (Ret E) := syncLiftCandidates task
  let readyRead : InstId → CStore E → P E Host (Ret E) := fun inst store =>
    .op .hostGet fun host => chooseNext (store.instCandidates (ready host) inst)
  let start : CStore E → P E Host (Ret E) := fun store =>
    ((match ArenaField.tasks.get? store task with
      | some info => pure info
      | none => internal "dangling arena id") : P E Host (Task E)) >>= fun info =>
    if info.state = .resolved then pure .unit else .op .get (readyRead info.inst)
  have body : syncLiftLoopBody ready task = .op .get start := by
    change Prog.op (S := Eff E Host) .get _ = Prog.op (S := Eff E Host) .get _
    congr 1
    funext store
    dsimp only [start, Prog.bind]
    cases ArenaField.tasks.get? store task
    · rfl
    · simp only [Prog.bind_eq, Prog.pure_eq, Prog.pure_bind']
      split <;> rfl
  have atStart : cfg.ctl = ⟨thread, .prog (.op .get start), frames⟩ :: rest := body ▸ focused
  have evaluates : start cfg.store = .op .get (readyRead entry.inst) := by
    simp only [start, found, pure_bind, ite_eq_right waiting]
  let residual := chooseNext (cfg.store.instCandidates (ready cfg.host) entry.inst)
  obtain ⟨otherFrames, otherRest, atOther, aligned⟩ := ReturnFrame.Paired.retarget paired focused
    (.prog residual) other.host
  have sameStore : cfg.store = other.store := (ReturnFrame.Paired.data paired).1
  have left := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) atStart
  rw [evaluates] at left
  have otherEvaluates : start other.store = .op .get (readyRead entry.inst) := sameStore ▸ evaluates
  have right := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) (body ▸ atOther)
  rw [otherEvaluates] at right
  refine ⟨{ cfg with ctl := ⟨thread, .prog residual, frames⟩ :: rest },
    { other with ctl := ⟨thread, .prog residual, otherFrames⟩ :: otherRest },
    .cons left (.cons (.get rfl) (.cons (.hostGet rfl) (.refl _))), .cons right (.cons (.get rfl) ?_), aligned⟩
  have same : residual = chooseNext (other.store.instCandidates (ready other.host) entry.inst) :=
    sameStore ▸ congrArg chooseNext agrees
  rw [same]
  exact .cons (.hostGet rfl) (.refl _)

end Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame
