module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Feedback
public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Prefix
public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Wiring

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness
open NestedTheta.Liveness.Demand.Proofs (ScopeAgrees valueAt get_read read_all read_selected gamma_read_agrees scope_snoc)
open Continuation (Stack)
open Continuation.Partial (Config Site)
open Continuation.Partial.Executable (Actions next? observe runFor observe_returned)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {entry results final : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {loops : Bool}
variable {member : Option (MemberSummaries V S)}

/-- The demanded ports after prepending captures use exactly the two ranges
in the application transfer. -/
theorem prepend_agrees {Ty : Type u} {F : Ty → Type w} {context params : Ports Ty}
    (wanted : Nat → Prop) (capsL capsR : Tuple F context) (argsL argsR : Tuple F params)
    (cap : ∀ {ty} (p : Port context ty), wanted p.index → capsL.get p = capsR.get p)
    (arg : ∀ {ty} (p : Port params ty), wanted (context.length + p.index) → argsL.get p = argsR.get p) :
    ∀ {ty} (p : Port (context ++ params) ty), wanted p.index →
      (prependContext argsL capsL).get p = (prependContext argsR capsR).get p := by
  induction capsL generalizing wanted with
  | nil =>
    cases capsR
    intro ty p live
    exact arg p (by simpa only [List.length_nil, Nat.zero_add] using live)
  | cons x xs ih =>
    cases capsR with
    | cons y ys =>
      intro ty p live
      cases p with
      | head => exact cap .head live
      | tail p =>
        apply ih (fun i => wanted (i + 1)) ys
        · exact fun p live => cap (.tail p) live
        · intro ty p live
          exact arg p (by simpa only [List.length_cons, Nat.succ_add] using live)
        · exact live

private theorem apply_agrees {params context : Ports (Ty V S)} (live : List Address)
    (captures : Wires entry [] context) (arguments : Wires entry past params)
    {entryL entryR : Tuple m.Val entry} {localsL localsR : Locals m.Val past}
    (agree : ScopeAgrees (applyReads live captures arguments) entryL entryR localsL localsR) :
    ScopeAgrees (scope := []) live
      (prependContext (arguments.read entryL localsL) (captures.read entryL PUnit.unit))
      (prependContext (arguments.read entryR localsR) (captures.read entryR PUnit.unit))
      PUnit.unit PUnit.unit := by
  intro ty origin needed
  cases origin with
  | output i _ => exact i.elim0
  | arg p =>
    apply prepend_agrees (fun i => Address.arg i ∈ live)
    · intro ty p present
      apply read_selected (fun _ i => live.contains (.arg i)) captures _ p (List.contains_iff_mem.2 present)
      intro ty origin selected
      cases origin with
      | output i _ => exact i.elim0
      | arg q => exact agree (.arg q) (List.mem_append_left _ selected)
    · intro ty p present
      exact read_selected (fun _ i => live.contains (.arg (context.length + i))) arguments
        (fun origin selected => agree origin (List.mem_append_right _ selected)) p (List.contains_iff_mem.2 present)
    · exact needed

private theorem call_agrees {params context : Ports (Ty V S)} (live : List Address)
    (captures : Wires entry past context) (arguments : Wires entry past params)
    {entryL entryR : Tuple m.Val entry} {localsL localsR : Locals m.Val past}
    (agree : ScopeAgrees (applyReads live captures arguments) entryL entryR localsL localsR) :
    ScopeAgrees (scope := []) live
      (prependContext (arguments.read entryL localsL) (captures.read entryL localsL))
      (prependContext (arguments.read entryR localsR) (captures.read entryR localsR))
      PUnit.unit PUnit.unit := by
  intro ty origin needed
  cases origin with
  | output i _ => exact i.elim0
  | arg p =>
    apply prepend_agrees (fun i => Address.arg i ∈ live)
    · intro ty p present
      exact read_selected (fun _ i => live.contains (.arg i)) captures
        (fun origin selected => agree origin (List.mem_append_left _ selected)) p (List.contains_iff_mem.2 present)
    · intro ty p present
      exact read_selected (fun _ i => live.contains (.arg (context.length + i))) arguments
        (fun origin selected => agree origin (List.mem_append_right _ selected)) p (List.contains_iff_mem.2 present)
    · exact needed

private theorem split_live {reads : List Address} {next : DemandPlan} {left right : Tuple m.Val entry}
    {localsL localsR : Locals m.Val past}
    (agree : ScopeAgrees (next.prepend past.length reads).live left right localsL localsR) :
    ScopeAgrees reads left right localsL localsR ∧
    ScopeAgrees (next.live.filter (fun a => !definedAt past.length a)) left right localsL localsR :=
  ⟨fun _ live => agree _ (List.mem_append_left _ live), fun _ live => agree _ (List.mem_append_right _ live)⟩

@[expose] def ResumeAgrees (actions : Actions m σ) (observed wanted : Demand) (depth : Option Nat)
    (left right : Stack m results final)
    (allowsL allowsR : Tuple m.Val results → Prop) : Prop :=
  ∀ (outL outR : Tuple m.Val results) (store : σ), wanted.Agrees outL outR →
    allowsL outL → allowsR outR →
    AtDepth actions observed depth ⟨.returned outL left, store⟩ ⟨.returned outR right, store⟩

private theorem ret_forwards (wires : Wires entry past results) (input : Tuple m.Val entry)
    (locals : Locals m.Val past) :
    (Code.ret (Op := Op) (loops := loops) (member := member) wires).Forwards input (wires.read input locals) := by
  intro ty p q source
  have read := get_read wires input locals p
  unfold Code.returnArg at source
  cases edge : wires.get p with
  | arg r =>
    rw [edge] at read
    rw [edge] at source
    cases source
    exact read
  | output i r => simp [edge] at source

private theorem output_observed {ty : Ty V S} {pc p : Nat} {plan : DemandPlan}
    (live : Address.output pc p ∈ plan.live) : (resultDemand pc plan).observes ty p = true := by
  cases ty with
  | state => rfl
  | control | value => exact List.contains_iff_mem.2 live

/-- The member-call premise covers any smaller finite observation depth. -/
@[expose] def MemberDispatch (actions : Actions m σ) (observed : Demand)
    {member : Option (MemberSummaries V S)} (guardL guardR : MemberResolution m member)
    (budget : Nat) (final : Ports (Ty V S)) : Prop :=
  match member with
  | none => True
  | some table =>
    ∀ (depth : Nat), depth ≤ budget →
      ∀ i : Fin table.members.length,
      let summary := table.at i
      ∀ (wanted : Demand) (fL fR : m.Val summary.fn.port) (capsL capsR : Tuple m.Val summary.captures)
        (argsL argsR : Tuple m.Val summary.fn.args) (store : σ) (left right : Stack m summary.fn.results final),
        guardL i fL capsL → guardR i fR capsR →
        ScopeAgrees (scope := []) (summary.live wanted)
          (prependContext argsL capsL) (prependContext argsR capsR) PUnit.unit PUnit.unit →
        ResumeAgrees actions observed wanted (some depth) left right (fun _ => True) (fun _ => True) →
        PrefixMatches actions observed depth
          ⟨.eval (.call fL argsL) left, store⟩ ⟨.eval (.call fR argsR) right, store⟩

private theorem dispatch_weaken {actions : Actions m σ} {observed : Demand}
    {guardL guardR : MemberResolution m member} {small large : Nat} (le : small ≤ large)
    (dispatch : MemberDispatch actions observed guardL guardR large final) :
    MemberDispatch actions observed guardL guardR small final := by
  cases member with
  | none => trivial
  | some table => exact fun n bound => dispatch n (bound.trans le)

theorem region (actions : Actions m σ) (observed : Demand) (code : Code Op entry past sigs results loops member) :
    ∀ (guardL guardR : MemberResolution m member) (depth : Option Nat),
      (loops = true → depth.isSome = true) →
      MemberDispatch actions observed guardL guardR (depth.getD 0) final →
      ∀ (wanted : Demand) (inputL inputR : Tuple m.Val entry) (localsL localsR : Locals m.Val past)
      (left right : Stack m results final) (store : σ),
      code.ResolvedAt guardL inputL localsL → code.ResolvedAt guardR inputR localsR →
      ScopeAgrees (code.plan wanted).live inputL inputR localsL localsR →
      ResumeAgrees actions observed wanted depth left right (code.Forwards inputL) (code.Forwards inputR) →
      AtDepth actions observed depth
        ⟨.eval (.region code.term inputL localsL) left, store⟩
        ⟨.eval (.region code.term inputR localsR) right, store⟩ := by
  induction code with
  | ret wires =>
    intro guardL guardR depth admitted dispatch wanted inputL inputR localsL localsR left right store _ _ agree resume
    apply depth_step rfl rfl
    exact resume _ _ store
      (fun p requested => read_selected wanted.observes wires
        (fun edge live => agree edge (List.mem_append_left _ live)) p requested)
      (ret_forwards wires inputL localsL) (ret_forwards wires inputR localsR)
  | @primitive entry results ins outs past sigs loops member opcode operands rest ih =>
    intro guardL guardR depth admitted dispatch wanted inputL inputR localsL localsR left right store resolvedL resolvedR agree resume
    obtain ⟨reads, old⟩ := split_live agree
    let frameL : Stack m outs final := .resume rest.term inputL localsL left
    let frameR : Stack m outs final := .resume rest.term inputR localsR right
    let needed := resultDemand past.length (rest.plan wanted)
    have after : ResumeAgrees actions observed needed depth frameL frameR (fun _ => True) (fun _ => True) := by
      intro outL outR middle demanded _ _
      apply depth_step rfl rfl
      exact ih guardL guardR depth admitted dispatch wanted inputL inputR _ _ left right middle (resolvedL outL) (resolvedR outR)
        (scope_snoc old (fun p live => demanded p (output_observed live))) resume
    let site : Site m := ⟨ins, outs, opcode, fun i => i.elim0, fun i => i.elim0, operands.read inputL localsL⟩
    have operands_eq := read_all operands reads
    have advanceL : next? actions (⟨.eval (.region (.primitive opcode operands rest : Code Op entry past _ results loops member).term
        inputL localsL) left, store⟩ : Config m σ final) = some ⟨.eval site.job frameL, store⟩ := rfl
    have advanceR : next? actions (⟨.eval (.region (.primitive opcode operands rest : Code Op entry past _ results loops member).term
        inputR localsR) right, store⟩ : Config m σ final) = some ⟨.eval site.job frameR, store⟩ := by
      change some (⟨.eval { site with input := operands.read inputR localsR }.job frameR, store⟩ :
        Config m σ final) = _
      rw [← operands_eq]
    apply depth_step advanceL advanceR
    cases tried : (actions.step site.opcode site.input).run store with
    | none => exact depth_blocked tried (fun value middle => after value value middle (fun _ _ => rfl) trivial trivial)
    | some outcome =>
      obtain ⟨value, middle⟩ := outcome
      have step (frame : Stack m outs final) :
          next? actions ⟨.eval site.job frame, store⟩ = some ⟨.returned value frame, middle⟩ := by
        change ((actions.step site.opcode site.input).run store).map
          (fun (v, s) => (⟨.returned v frame, s⟩ : Config m σ final)) = _
        rw [tried]
        rfl
      exact depth_step (step frameL) (step frameR) (after value value middle (fun _ _ => rfl) trivial trivial)
  | @apply entry results context fn past sigs bodySigs loops member target captures body arguments rest ihBody ihRest =>
    intro guardL guardR depth admitted dispatch wanted inputL inputR localsL localsR left right store resolvedL resolvedR agree resume
    obtain ⟨reads, old⟩ := split_live agree
    obtain ⟨targetL, bodyL, restL⟩ := resolvedL
    obtain ⟨targetR, bodyR, restR⟩ := resolvedR
    let frameL : Stack m fn.results final := .resume rest.term inputL localsL left
    let frameR : Stack m fn.results final := .resume rest.term inputR localsR right
    let needed := resultDemand past.length (rest.plan wanted)
    have after : ResumeAgrees actions observed needed depth frameL frameR (fun _ => True) (fun _ => True) := by
      intro outL outR middle demanded _ _
      apply depth_step rfl rfl
      exact ihRest guardL guardR depth admitted dispatch wanted inputL inputR _ _ left right middle (restL outL) (restR outR)
        (scope_snoc old (fun p live => demanded p (output_observed live))) resume
    let capL := captures.read inputL PUnit.unit
    let capR := captures.read inputR PUnit.unit
    let argL := arguments.read inputL localsL
    let argR := arguments.read inputR localsR
    have openBody (f : m.Val fn.port) (capture : Tuple m.Val context) (arg : Tuple m.Val fn.args)
        (frame : Stack m fn.results final) (resolved : f = .closure capture body.term.toGraph) :
        next? actions ⟨.eval (.call f arg) frame, store⟩ =
          some ⟨.eval (.region body.term (prependContext arg capture) PUnit.unit) frame, store⟩ := by
      subst f
      change some (⟨.eval (.region body.term.toGraph.toTerm (prependContext arg capture) PUnit.unit) frame, store⟩ :
        Config m σ final) = _
      rw [NestedTheta.Term.toTerm_toGraph]
    apply depth_step rfl rfl
    apply depth_step rfl rfl
    apply depth_step (openBody _ capL argL frameL targetL) (openBody _ capR argR frameR targetR)
    exact ihBody guardL guardR depth admitted dispatch needed _ _ PUnit.unit PUnit.unit frameL frameR store (bodyL argL) (bodyR argR)
      (apply_agrees _ captures arguments reads) (fun l r s h _ _ => after l r s h trivial trivial)
  | @gamma entry results captures outs past sigs loops member extra armSigs selector wires arms rest ihArm ihRest =>
    intro guardL guardR depth admitted dispatch wanted inputL inputR localsL localsR left right store resolvedL resolvedR agree resume
    obtain ⟨reads, old⟩ := split_live agree
    let needed := resultDemand past.length (rest.plan wanted)
    obtain ⟨tags, capturesAgree⟩ :=
      gamma_read_agrees selector wires (fun i => ((arms i).plan needed).live) reads
    let tagL := valueAt selector inputL localsL
    let tagR := valueAt selector inputR localsR
    have sameArm : tagL.selector = tagR.selector := congrArg Colour.selector tags
    let frameL : Stack m outs final := .resume rest.term inputL localsL left
    let frameR : Stack m outs final := .resume rest.term inputR localsR right
    have after : ResumeAgrees actions observed needed depth frameL frameR ((arms tagL.selector).Forwards (wires.read inputL localsL))
        ((arms tagL.selector).Forwards (wires.read inputR localsR)) := by
      intro outL outR middle demanded forwardedL forwardedR
      apply depth_step rfl rfl
      exact ihRest guardL guardR depth admitted dispatch wanted inputL inputR _ _ left right middle
        (resolvedL.2 _ _ forwardedL) (resolvedR.2 tagL.selector _ forwardedR)
        (scope_snoc old (fun p live => demanded p (output_observed live))) resume
    apply depth_step rfl rfl
    apply depth_step rfl rfl
    change AtDepth actions observed depth
      ⟨.eval (.region (arms tagL.selector).term (wires.read inputL localsL) PUnit.unit) frameL, store⟩
      ⟨.eval (.region (arms tagR.selector).term (wires.read inputR localsR) PUnit.unit) frameR, store⟩
    rw [← sameArm]
    exact ihArm tagL.selector guardL guardR depth admitted dispatch needed _ _ PUnit.unit PUnit.unit frameL frameR store
      (resolvedL.1 _) (resolvedR.1 _) (capturesAgree tagL.selector) after

  | @theta entry results carried past sigs bodySigs member wires body rest ihBody ihRest =>
    intro guardL guardR depth admitted dispatch wanted inputL inputR localsL localsR left right store resolvedL resolvedR agree resume
    cases depth with
    | none => exact False.elim (by simpa using admitted rfl)
    | some depth =>
      obtain ⟨reads, old⟩ := split_live agree
      let exit := resultDemand past.length (rest.plan wanted)
      let live := body.feedbackLive exit
      let frameL : Stack m carried final := .resume rest.term inputL localsL left
      let frameR : Stack m carried final := .resume rest.term inputR localsR right
      have after : ResumeAgrees actions observed exit (some depth) frameL frameR (fun _ => True) (fun _ => True) := by
        intro outL outR middle demanded _ _
        apply depth_step rfl rfl
        exact ihRest guardL guardR (some depth) (by simp) dispatch wanted inputL inputR _ _ left right middle (resolvedL.2 outL) (resolvedR.2 outR)
          (scope_snoc old (fun p live => demanded p (output_observed live))) resume
      let firstL := wires.read inputL localsL
      let firstR := wires.read inputR localsR
      have runLoop (n : Nat) (nowL nowR : Tuple m.Val carried) (current : σ)
          (staticL : body.Stable firstL nowL) (staticR : body.Stable firstR nowR)
          (related : Feedback.Agrees live nowL nowR)
          (finish : ResumeAgrees actions observed exit (some n) frameL frameR (fun _ => True) (fun _ => True))
          (canCall : MemberDispatch actions observed guardL guardR n final) :
          PrefixMatches actions observed n
            ⟨.eval (.iteration body.term nowL) frameL, current⟩
            ⟨.eval (.iteration body.term nowR) frameR, current⟩ := by
        induction n generalizing nowL nowR current with
        | zero => exact .cut _ _
        | succ n ih =>
          have finish' : ResumeAgrees actions observed exit (some n) frameL frameR (fun _ => True) (fun _ => True) :=
            fun l r s h _ _ => prefix_mono (Nat.le_succ n) (finish l r s h trivial trivial)
          apply PrefixMatches.step rfl rfl
          have smaller := dispatch_weaken (Nat.le_succ n) canCall
          apply ihBody guardL guardR (some n) (by simp) smaller (Feedback.bodyDemand exit live) nowL nowR PUnit.unit PUnit.unit
            (.loop body.term frameL) (.loop body.term frameR) current
            (resolvedL.1 nowL staticL) (resolvedR.1 nowR staticR)
          · intro ty origin needed
            cases origin with
            | output i _ => exact i.elim0
            | arg p => exact related p ((includes_feedback_iff body exit p).2 needed)
          · intro packetL packetR middle matched forwardedL forwardedR
            cases packetL with
            | cons tag outL =>
              cases packetR with
              | cons other outR =>
                have tags : tag = other := matched .head rfl
                subst other
                have step (out : Tuple m.Val carried) (frame : Stack m carried final) :
                    next? actions ⟨.returned (.cons tag out) (.loop body.term frame), middle⟩ =
                      some ⟨Continuation.State.finishLoop body.term tag out frame, middle⟩ := rfl
                apply depth_step (step outL frameL) (step outR frameR)
                cases decision : (tag.selector.val == 1) with
                | false =>
                  simp only [Continuation.State.finishLoop, decision, Bool.false_eq_true, ite_false]
                  apply finish' _ _ middle _ trivial trivial
                  intro ty p demanded
                  apply matched (.tail p)
                  cases ty with
                  | state => rfl
                  | control | value => exact Bool.or_eq_true_iff.2 (Or.inl demanded)
                | true =>
                  simp only [Continuation.State.finishLoop, decision, ite_true]
                  apply ih outL outR middle _ _ _ finish' smaller
                  · exact fun p h => (forwardedL (.tail p) p h).trans (staticL p h)
                  · exact fun p h => (forwardedR (.tail p) p h).trans (staticR p h)
                  · intro ty p demanded
                    apply matched (.tail p)
                    cases ty with
                    | state => rfl
                    | control | value => exact Bool.or_eq_true_iff.2 (Or.inr demanded)
      apply depth_step rfl rfl
      apply depth_step rfl rfl
      exact runLoop depth firstL firstR store (fun _ _ => rfl) (fun _ _ => rfl)
        (fun p livePort => read_selected (fun _ i => Feedback.includes live i) wires reads p livePort) after dispatch

  | @callAt entry results past sigs table i target captures arguments rest ihRest =>
    intro guardL guardR depth admitted dispatch wanted inputL inputR localsL localsR left right store
      resolvedL resolvedR agree resume
    cases depth with
    | none => exact False.elim (by simpa using admitted rfl)
    | some depth =>
      obtain ⟨reads, old⟩ := split_live agree
      let needed := resultDemand past.length (rest.plan wanted)
      let summary := table.at i
      let frameL : Stack m summary.fn.results final := .resume rest.term inputL localsL left
      let frameR : Stack m summary.fn.results final := .resume rest.term inputR localsR right
      have after : ResumeAgrees actions observed needed (some depth) frameL frameR (fun _ => True) (fun _ => True) := by
        intro outL outR middle demanded _ _
        apply depth_step rfl rfl
        exact ihRest guardL guardR (some depth) (by simp) dispatch wanted inputL inputR _ _ left right middle
          (resolvedL.2 outL) (resolvedR.2 outR) (scope_snoc old (fun p live => demanded p (output_observed live))) resume
      apply depth_step rfl rfl
      apply depth_step rfl rfl
      exact dispatch depth (Nat.le_refl _) i needed _ _ _ _ _ _ store frameL frameR
        resolvedL.1 resolvedR.1 (call_agrees _ captures arguments reads) after

private theorem plan_live (code : Code Op entry past sigs results loops member) (demand : Demand) :
    (code.plan demand).live = sweep (code.plan demand).reads past.length := by
  induction code with
  | ret => rfl
  | primitive _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]
  | apply _ _ _ _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]
  | gamma _ _ _ _ _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]
  | theta _ _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]

  | callAt _ _ _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]

theorem mem_liveIn_iff (code : Code Op entry [] sigs results loops member) (demand : Demand) (a : Address) :
    a ∈ code.liveIn demand ↔ a ∈ (code.liveness demand).mayOut 0 := by
  simpa only [Code.liveIn, List.mem_eraseDups, plan_live, List.length_nil,
    Code.liveness, List.drop_zero] using mem_sweep_iff (code.plan demand).reads 0 a

theorem settles {actions : Actions m σ} {demand : Demand} {left right : Config m σ results}
    (checked : Matches actions demand left right) :
    ∃ fuel, EndpointsAgree actions demand
      (observe actions (runFor actions fuel left)) (observe actions (runFor actions fuel right)) := by
  induction checked with
  | returned agree =>
    exact ⟨0, by rw [runFor, runFor, observe_returned.2 rfl, observe_returned.2 rfl]; exact .returned agree⟩
  | step stepL stepR _ ih =>
    obtain ⟨fuel, related⟩ := ih
    exact ⟨fuel + 1, by simpa only [runFor, stepL, stepR] using related⟩
  | @blocked site left right store undefined resume _ =>
    refine ⟨0, ?_⟩
    rw [runFor, runFor, sees_block left store undefined, sees_block right store undefined]
    exact .blocked resume

private theorem calls_at_depth {fn : Function V S} {context : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) [] sigs fn.results loops)
    (depth : Option Nat) (admitted : loops = true → depth.isSome = true)
    (actions : Actions m σ) (demand : Demand) (fL fR : m.Val fn.port)
    (capsL capsR : Tuple m.Val context) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closureL : fL = .closure capsL code.term.toGraph)
    (closureR : fR = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    AtDepth actions demand depth
      ⟨Continuation.start (.call fL argsL), store⟩
      ⟨Continuation.start (.call fR argsR), store⟩ := by
  subst fL fR
  have entry_step (caps : Tuple m.Val context) (args : Tuple m.Val fn.args) :
      next? actions ⟨Continuation.start (.call (.closure caps code.term.toGraph) args), store⟩ =
        some ⟨.eval (.region code.term (prependContext args caps) PUnit.unit) .halt, store⟩ := by
    change some (⟨.eval (.region code.term.toGraph.toTerm (prependContext args caps) PUnit.unit) .halt, store⟩ :
      Config m σ fn.results) = _
    rw [NestedTheta.Term.toTerm_toGraph]
  apply depth_step (entry_step capsL argsL) (entry_step capsR argsR)
  apply region actions demand code PUnit.unit PUnit.unit depth admitted trivial demand _ _ PUnit.unit PUnit.unit .halt .halt store (resolvedL PUnit.unit) (resolvedR PUnit.unit)
  · intro ty source live
    cases source with
    | output i _ => exact i.elim0
    | arg p => exact agree p (List.mem_eraseDups.2 live)
  · intro _ _ _ equal _ _
    cases depth with
    | none => exact Matches.returned equal
    | some n =>
      cases n with
      | zero => exact PrefixMatches.cut _ _
      | succ n => exact PrefixMatches.returned equal

theorem matches_calls {fn : Function V S} {context : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) [] sigs fn.results)
    (actions : Actions m σ) (demand : Demand) (fL fR : m.Val fn.port)
    (capsL capsR : Tuple m.Val context) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closureL : fL = .closure capsL code.term.toGraph)
    (closureR : fR = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    Matches actions demand
      ⟨Continuation.start (.call fL argsL), store⟩
      ⟨Continuation.start (.call fR argsR), store⟩ :=
  calls_at_depth code none (by simp) actions demand fL fR capsL capsR argsL argsR store
    closureL closureR resolvedL resolvedR agree

theorem calls_prefix {fn : Function V S} {context : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) [] sigs fn.results loops)
    (actions : Actions m σ) (demand : Demand) (fL fR : m.Val fn.port)
    (capsL capsR : Tuple m.Val context) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closureL : fL = .closure capsL code.term.toGraph)
    (closureR : fR = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (.call fL argsL), store⟩
      ⟨Continuation.start (.call fR argsR), store⟩ :=
  fun depth => calls_at_depth code (some depth) (by simp) actions demand fL fR capsL capsR argsL argsR store
    closureL closureR resolvedL resolvedR agree

theorem linked_runs_agree {fn : Function V S} {context : Ports (Ty V S)}
    {imports exports : Ports (Ty V S)} {moduleSigs : List (Ports (Ty V S))}
    (code : Code Op (context ++ fn.args) [] sigs fn.results)
    (actions : Actions m σ) (demand : Demand) (graph : Omega Op imports exports moduleSigs)
    (unitId : Nat) (port : Port exports fn.port)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val fn.args) (initial : σ)
    {exportsL exportsR : Tuple m.Val exports} {middle : σ}
    {capsL capsR : Tuple m.Val context}
    (linkedL : Executable.link actions unitId graph inputsL initial = .linked exportsL middle)
    (linkedR : Executable.link actions unitId graph inputsR initial = .linked exportsR middle)
    (closureL : exportsL.get port = .closure capsL code.term.toGraph)
    (closureR : exportsR.get port = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∃ fuel observedL observedR,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok observedL ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok observedR ∧
      EndpointsAgree actions demand observedL observedR := by
  obtain ⟨fuel, related⟩ := settles (matches_calls code actions demand _ _ capsL capsR argsL argsR middle
    closureL closureR resolvedL resolvedR agree)
  refine ⟨fuel, _, _, ?_, ?_, related⟩
  · simp only [Executable.run, Executable.start, linkedL, Except.map]
    rfl
  · simp only [Executable.run, Executable.start, linkedR, Except.map]
    rfl

theorem linked_prefixes_agree {fn : Function V S} {context : Ports (Ty V S)}
    {imports exports : Ports (Ty V S)} {moduleSigs : List (Ports (Ty V S))}
    (code : Code Op (context ++ fn.args) [] sigs fn.results loops)
    (actions : Actions m σ) (demand : Demand) (fuel after : Nat) (graph : Omega Op imports exports moduleSigs)
    (unitId : Nat) (port : Port exports fn.port)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val fn.args) (initial : σ)
    {exportsL exportsR : Tuple m.Val exports} {middle : σ}
    {capsL capsR : Tuple m.Val context}
    (linkedL : Executable.link actions unitId graph inputsL initial = .linked exportsL middle)
    (linkedR : Executable.link actions unitId graph inputsR initial = .linked exportsR middle)
    (closureL : exportsL.get port = .closure capsL code.term.toGraph)
    (closureR : exportsR.get port = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∃ observedL observedR,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok observedL ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok observedR ∧
      PrefixObservationsAgree actions demand after observedL observedR := by
  have related := prefix_observes fuel after
    (calls_prefix code actions demand _ _ capsL capsR argsL argsR middle
      closureL closureR resolvedL resolvedR agree _)
  refine ⟨_, _, ?_, ?_, related⟩
  · simp only [Executable.run, Executable.start, linkedL, Except.map]
    rfl
  · simp only [Executable.run, Executable.start, linkedR, Except.map]
    rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
