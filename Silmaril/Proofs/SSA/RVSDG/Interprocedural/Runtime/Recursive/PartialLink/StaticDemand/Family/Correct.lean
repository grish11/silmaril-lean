module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Defs
public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness (Demand)
open NestedTheta.Liveness.Demand.Proofs (ScopeAgrees valueAt)
open Continuation (Stack)
open Continuation.Partial (Config)
open Continuation.Partial.Executable (Actions next? observe runFor)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports final : Ports (Ty V S)}
variable (family : Family Op table imports)

private theorem get_ofTable {n : Nat} {F : Fin n → Type w} (values : (i : Fin n) → F i) (i : Fin n) :
    (Definitions.ofTable n values).get i = values i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => exact Fin.cases rfl (fun j => ih (fun k => values k.succ) j) i

theorem member_get {F : Ty V S → Type w} (members : List (Function V S))
    (values : (i : Fin members.length) → F members[i].port) (i : Fin members.length) :
    (memberValues members values).get (memberPort members i) = values i := by
  induction members with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih (fun k => values k.succ) j) i

theorem family_opens (captured : Tuple m.Val family.context) (i : Fin table.members.length)
    (args : Tuple m.Val (table.at i).fn.args) :
    Job.openClosure m (family.memberValue captured i) args =
      .region (family.body i).term (family.entry captured i args) PUnit.unit := by
  have chosen : family.group.toGraph.definitions i =
      LambdaTerm.toGraph
        ⟨memberPorts table.members ++ (table.at i).captures, family.memberWires i,
          family.sigs i, (family.body i).term⟩ := by
    change (family.group.definitions.get i).toGraph = _
    unfold Family.group
    rw [get_ofTable]
  change Job.region (family.group.toGraph.definitions i).body.toTerm
    (prependContext args ((family.group.toGraph.definitions i).captures.read
      (prependContext (family.references captured) captured)
      (memberPrefix table.members i.val (family.memberValue captured))))
    (PUnit.unit : Locals m.Val []) = _
  rw [chosen]
  change Job.region (family.body i).term.toGraph.toTerm (family.entry captured i args)
    (PUnit.unit : Locals m.Val []) = _
  rw [NestedTheta.Term.toTerm_toGraph]

private theorem ordinary_agrees {Ty : Type u} {F : Ty → Type w} {refs caps params : Ports Ty}
    (wanted : Nat → Prop) (refsL refsR : Tuple F refs)
    (capsL capsR : Tuple F caps) (argsL argsR : Tuple F params)
    (onlyOrdinary : ∀ i, i < refs.length → ¬ wanted i)
    (agree : ∀ {ty} (p : Port (caps ++ params) ty), wanted (refs.length + p.index) →
      (prependContext argsL capsL).get p = (prependContext argsR capsR).get p) :
    ∀ {ty} (p : Port ((refs ++ caps) ++ params) ty), wanted p.index →
      (prependContext argsL (prependContext capsL refsL)).get p =
      (prependContext argsR (prependContext capsR refsR)).get p := by
  induction refsL generalizing wanted with
  | nil =>
    cases refsR
    intro ty p live
    exact agree p (by simpa only [List.length_nil, Nat.zero_add] using live)
  | cons x xs ih =>
    cases refsR with
    | cons y ys =>
      intro ty p live
      cases p with
      | head => exact False.elim (onlyOrdinary 0 (Nat.zero_lt_succ _) live)
      | tail p =>
        apply ih (fun i => wanted (i + 1)) ys
        · exact fun i inside => onlyOrdinary (i + 1) (Nat.succ_lt_succ inside)
        · intro ty q active
          exact agree q (by simpa only [List.length_cons, Nat.succ_add] using active)
        · exact live

private theorem body_agrees (i : Fin table.members.length) (wanted : Demand)
    {capturedL capturedR : Tuple m.Val family.context} {argsL argsR : Tuple m.Val (table.at i).fn.args}
    (readyL : family.Ready capturedL) (readyR : family.Ready capturedR)
    (live : ScopeAgrees (scope := []) (table.live i wanted)
      (prependContext argsL (family.capturedAt capturedL i))
      (prependContext argsR (family.capturedAt capturedR i)) PUnit.unit PUnit.unit) :
    ScopeAgrees (scope := []) ((family.body i).plan wanted).live
      (family.entry capturedL i argsL) (family.entry capturedR i argsR) PUnit.unit PUnit.unit := by
  intro ty source needed
  cases source with
  | output j _ => exact j.elim0
  | arg p =>
    simp only [valueAt, Family.entry, (readyL i).1, (readyR i).1]
    apply ordinary_agrees (fun j => Address.arg j ∈ ((family.body i).plan wanted).live)
    · exact (family.closed i wanted).1
    · exact fun q h => live (.arg q) ((family.closed i wanted).2 q.index h)
    · exact needed

private theorem member_prefix (actions : Actions m σ) (observed : Demand)
    (capturedL capturedR : Tuple m.Val family.context)
    (readyL : family.Ready capturedL) (readyR : family.Ready capturedR) (budget : Nat) :
    ∀ (i : Fin table.members.length) (wanted : Demand) (argsL argsR : Tuple m.Val (table.at i).fn.args)
      (store : σ) (left right : Stack m (table.at i).fn.results final),
      ScopeAgrees (scope := []) (table.live i wanted)
        (prependContext argsL (family.capturedAt capturedL i))
        (prependContext argsR (family.capturedAt capturedR i)) PUnit.unit PUnit.unit →
      ResumeAgrees actions observed wanted (some budget) left right (fun _ => True) (fun _ => True) →
      PrefixMatches actions observed budget
        ⟨.eval (.call (family.memberValue capturedL i) argsL) left, store⟩
        ⟨.eval (.call (family.memberValue capturedR i) argsR) right, store⟩ := by
  induction budget using Nat.strong_induction_on with
  | ind budget ih =>
    intro i wanted argsL argsR store left right live finish
    cases budget with
    | zero => exact .cut _ _
    | succ n =>
      have enter (captured : Tuple m.Val family.context) (args : Tuple m.Val (table.at i).fn.args)
          (frame : Stack m (table.at i).fn.results final) :
          next? actions ⟨.eval (.call (family.memberValue captured i) args) frame, store⟩ =
            some ⟨.eval (.region (family.body i).term (family.entry captured i args) PUnit.unit) frame, store⟩ := by
        change some (⟨.eval (Job.openClosure m (family.memberValue captured i) args) frame, store⟩ :
          Config m σ final) = _
        rw [family_opens family captured i args]
      have dispatch : MemberDispatch actions observed (family.guard capturedL) (family.guard capturedR) n final := by
        intro depth bounded j
        dsimp only
        intro requested fL fR capL capR argL argR middle frameL frameR hL hR agree resume
        rcases hL with ⟨targetL, capturesL⟩
        rcases hR with ⟨targetR, capturesR⟩
        rw [targetL, targetR]
        rw [capturesL, capturesR] at agree
        exact ih depth (Nat.lt_succ_of_le bounded) j requested argL argR middle frameL frameR agree resume
      apply PrefixMatches.step (enter capturedL argsL left) (enter capturedR argsR right)
      apply region actions observed (family.body i) (family.guard capturedL) (family.guard capturedR)
        (some n) (by simp) dispatch wanted _ _ PUnit.unit PUnit.unit left right store
        ((readyL i).2 argsL PUnit.unit) ((readyR i).2 argsR PUnit.unit) (body_agrees family i wanted readyL readyR live)
      intro outL outR middle agree _ _
      exact prefix_mono (Nat.le_succ n) (finish outL outR middle agree trivial trivial)

/-- Dispatch into the closed group with any related suffix, including
a frame belonging to an enclosing exported λ. -/
theorem family_dispatch (actions : Actions m σ) (observed : Demand)
    (capturedL capturedR : Tuple m.Val family.context)
    (readyL : family.Ready capturedL) (readyR : family.Ready capturedR) (budget : Nat) :
    MemberDispatch actions observed (family.guard capturedL) (family.guard capturedR) budget final := by
  intro depth _ i
  dsimp only
  intro wanted fL fR capL capR argsL argsR store left right hL hR live resume
  rcases hL with ⟨targetL, capturesL⟩
  rcases hR with ⟨targetR, capturesR⟩
  rw [targetL, targetR]
  rw [capturesL, capturesR] at live
  exact member_prefix family actions observed capturedL capturedR readyL readyR depth i wanted argsL argsR
    store left right live resume

theorem family_calls (i : Fin table.members.length) (actions : Actions m σ) (demand : Demand)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val (table.at i).fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs i demand importedL importedR argsL argsR) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (family.invocation i importedL argsL), store⟩
      ⟨Continuation.start (family.invocation i importedR argsR), store⟩ := by
  intro depth
  apply member_prefix family actions demand _ _ readyL readyR depth i demand argsL argsR store .halt .halt
  · intro ty source needed
    cases source with
    | output j _ => exact j.elim0
    | arg p => exact agree p needed
  · intro outL outR middle demanded _ _
    cases depth with
    | zero => exact PrefixMatches.cut _ _
    | succ n => exact PrefixMatches.returned demanded

theorem family_starts (i : Fin table.members.length) (actions : Actions m σ) (unitId : Nat)
    (imported : Tuple m.Val imports) (args : Tuple m.Val (table.at i).fn.args) (store : σ) :
    Executable.start actions unitId (family.graph i) imported .head args store =
      .ok ⟨Continuation.start (family.invocation i imported args), store⟩ := by
  let captured := family.captures.read imported PUnit.unit
  change Except.ok (⟨Continuation.start (.call ((family.references captured).get (memberPort table.members i)) args),
    store⟩ : Config m σ (table.at i).fn.results) = _
  exact congrArg (fun f : m.Val (table.at i).fn.port =>
    Except.ok (⟨Continuation.start (.call f args), store⟩ : Config m σ (table.at i).fn.results))
    (member_get table.members (family.memberValue captured) i)

theorem family_linked (i : Fin table.members.length) (actions : Actions m σ) (demand : Demand)
    (fuel after unitId : Nat) (importedL importedR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val (table.at i).fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs i demand importedL importedR argsL argsR) :
    ∃ left right,
      family.run i actions fuel unitId importedL argsL store = .ok left ∧
      family.run i actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right := by
  have related := prefix_observes fuel after (family_calls family i actions demand importedL importedR
    argsL argsR store readyL readyR agree _)
  refine ⟨_, _, ?_, ?_, related⟩
  · simp only [Family.run, Executable.run, family_starts]
    rfl
  · simp only [Family.run, Executable.run, family_starts]
    rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
