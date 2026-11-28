module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Compilation

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Proofs

open RVSDG (Tuple)
open Simple (Exec WhileTrace)
open Simple.Revert.While.Region (Certificate)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}
variable (cert : Certificate g allowInvariant) (m : TotalModel P)

private abbrev Store (carried : List (Ty Data)) := Tuple m.toPEG.Value carried
private abbrev Tagged (carried : List (Ty Data)) := Tuple m.toPEG.Value (.bool :: carried)

private theorem bodyResult_inj {a b : Bool} {xs ys : Store m carried}
    (h : RVSDG.Theta.bodyResult (model m) a (encode m xs) =
      RVSDG.Theta.bodyResult (model m) b (encode m ys)) : a = b ∧ xs = ys := by
  have tags := congrArg (fun v : Tuple (model m).Val (RVSDG.Theta.BodyResults (valuePorts carried)) =>
    (v.get .head).down.val) h
  have words := congrArg (fun v : Tuple (model m).Val (RVSDG.Theta.BodyResults (valuePorts carried)) =>
    fromPorts (F := (model m).Val) carried (match v with | .cons _ rest => rest)) h
  refine ⟨?_, ?_⟩
  · cases a <;> cases b <;> first | rfl | contradiction
  · simpa only [RVSDG.Theta.bodyResult, encode, from_toPorts] using words

private theorem body_step (input output : Store m carried) (again : Bool) :
    (compile cert).body.run (model m) (encode m input) =
      RVSDG.Theta.bodyResult (model m) again (encode m output) ↔
    ∃ old, cert.guard.lower.runLoopFree m.toPEG input = some (.cons ⟨again⟩ old) ∧
      (if again then cert.update.lower.runLoopFree m.toPEG old = some output else output = old) := by
  obtain ⟨⟨flag⟩, old, next, guarded, updated, ran⟩ := body_run m cert input
  rw [ran, guarded]
  constructor
  · intro eval
    obtain ⟨rfl, rfl⟩ := bodyResult_inj m eval
    refine ⟨old, rfl, ?_⟩
    cases flag
    · rfl
    · exact updated
  · rintro ⟨found, tested, step⟩
    have same : (.cons ⟨flag⟩ old : Tagged m carried) = .cons ⟨again⟩ found := Option.some.inj tested
    cases same
    cases again
    · have eq : output = old := step
      cases eq
      rfl
    · have eq : next = output := Option.some.inj (updated.symm.trans step)
      cases eq
      rfl

private theorem run_body (flag : ULift Bool) (old : Store m carried) :
    cert.body.runLoopFree m.toPEG (.cons flag old) =
      (cert.update.lower.runLoopFree m.toPEG old).bind (cert.guard.lower.runLoopFree m.toPEG) := by
  change (cert.update.lower.runLoopFree m.toPEG
    (((Simple.ports carried).map fun _ p => p.tail).map fun _ p =>
      (Tuple.cons (F := m.toPEG.Value) (t := .bool) flag old).get p)).bind _ = _
  rw [project_old]

private theorem trace_to_returns {k : Nat} {start final : Tagged m carried}
    (trace : WhileTrace m.toPEG (.var .head) cert.body.enableWhile k start final)
    (input : Store m carried) (tested : cert.guard.lower.runLoopFree m.toPEG input = some start) :
    (compile cert).Returns (model m) (encode m input)
      (encode m (carriedValues final)) := by
  induction trace generalizing input with
  | @stop store test =>
    cases store with
    | cons flag old =>
      have flagEq : flag = ⟨false⟩ := Option.some.inj test
      cases flagEq
      exact RVSDG.Theta.Iterate.stop ((body_step cert m input old false).mpr ⟨old, tested, rfl⟩)
  | @step k start next final test ran rest ih =>
    cases start with
    | cons flag old =>
      have flagEq : flag = ⟨true⟩ := Option.some.inj test
      cases flagEq
      obtain ⟨after, update⟩ := (schedules_total m cert).update old
      have guard := Exec.deterministic (cert.body.runLoopFree_enableWhile (.cons ⟨true⟩ old)) ran
      rw [run_body, update] at guard
      exact RVSDG.Theta.Iterate.again ((body_step cert m input after true).mpr ⟨old, tested, update⟩)
        (ih after guard)

private theorem returns_to_trace {input output : Tuple (model m).Val (valuePorts carried)}
    (ran : (compile cert).Returns (model m) input output) :
    ∃ (k : Nat) (start final : Tagged m carried),
      cert.guard.lower.runLoopFree m.toPEG (fromPorts (F := (model m).Val) carried input) = some start ∧
      WhileTrace m.toPEG (.var .head) cert.body.enableWhile k start final ∧
      carriedValues final = fromPorts (F := (model m).Val) carried output := by
  change RVSDG.Theta.Iterate _ input output at ran
  induction ran with
  | @stop input output completed =>
    let start := fromPorts (F := (model m).Val) carried input
    let finish := fromPorts (F := (model m).Val) carried output
    obtain ⟨old, tested, returned⟩ := (body_step cert m start finish false).mp
      (by simpa only [start, finish, encode, to_fromPorts] using completed)
    exact ⟨0, .cons ⟨false⟩ old, .cons ⟨false⟩ old, tested, .stop rfl, returned.symm⟩
  | @again input next output completed _ ih =>
    let start := fromPorts (F := (model m).Val) carried input
    let after := fromPorts (F := (model m).Val) carried next
    obtain ⟨old, tested, updated⟩ := (body_step cert m start after true).mp
      (by simpa only [start, after, encode, to_fromPorts] using completed)
    obtain ⟨k, tagged, final, guard, trace, returned⟩ := ih
    have run : cert.body.runLoopFree m.toPEG (.cons ⟨true⟩ old) = some tagged := by
      rw [run_body, show cert.update.lower.runLoopFree m.toPEG old = some after from updated]
      exact guard
    exact ⟨k + 1, .cons ⟨true⟩ old, final, tested,
      .step rfl (run ▸ cert.body.runLoopFree_enableWhile (.cons ⟨true⟩ old)) trace, returned⟩

/-- The actual θ return relation agrees with the reversion trace, with a
θ restart for every successful while step and a mandatory stop activation. -/
theorem returns_iff_trace (input output : Tuple m.toPEG.Value carried) :
    (compile cert).Returns (model m) (encode m input) (encode m output) ↔
      ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
        cert.guard.lower.runLoopFree m.toPEG input = some start ∧
        WhileTrace m.toPEG (.var .head) cert.body.enableWhile k start final ∧
        carriedValues final = output := by
  constructor
  · intro ran
    simpa only [encode, from_toPorts] using returns_to_trace cert m ran
  · rintro ⟨k, start, final, guard, trace, rfl⟩
    exact trace_to_returns cert m trace input guard

variable (input : Tuple m.toPEG.Value carried)
variable (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = ⟨!b⟩)

include neg

theorem return_at_firstExit (idx : Index 1) (value : m.toPEG.Value result)
    (defined : g.observe m.toPEG (g.denote m.toPEG input cert.demandWellFounded) idx =
      .cons (some value) .nil) :
    ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
      cert.guard.lower.runLoopFree m.toPEG input = some start ∧
      cert.ExitWitness m.toPEG (g.denote m.toPEG input cert.demandWellFounded) idx k start final value ∧
      (compile cert).Returns (model m) (encode m input)
        (encode m (carriedValues final)) := by
  obtain ⟨k, start, final, tested, exit⟩ := cert.exitWitness_of_defined m.toPEG input
    (schedules_total m cert) (fun b => congrArg some (neg b)) idx defined
  exact ⟨k, start, final, tested, exit, trace_to_returns cert m exit.trace input tested⟩

theorem returns_iff_observe (idx : Index 1) (value : m.toPEG.Value result) :
    (∃ output : Tuple m.toPEG.Value carried,
      (compile cert).Returns (model m) (encode m input) (encode m output) ∧
      output.get cert.descriptor.returnSlot = value) ↔
    g.observe m.toPEG (g.denote m.toPEG input cert.demandWellFounded) idx = .cons (some value) .nil := by
  constructor
  · rintro ⟨output, returns, selected⟩
    obtain ⟨_, start, final, tested, trace, same⟩ := (returns_iff_trace cert m input output).mp returns
    have projected : final.get (.tail cert.descriptor.returnSlot) = value := by
      cases final
      exact (congrArg (fun xs : Store m carried => xs.get cert.descriptor.returnSlot) same).trans selected
    exact cert.observe_of_returns m.toPEG input (fun b => congrArg some (neg b)) idx
      ⟨final, .seq (tested ▸ cert.guard.lower.runLoopFree_enableWhile input) trace.exec, projected⟩
  · intro defined
    obtain ⟨_, _, final, _, exit, returned⟩ := return_at_firstExit cert m input neg idx value defined
    cases final with
    | cons _ old => exact ⟨old, returned, exit.returned⟩

end Silmaril.SSA.PEG.Bridge.Theta.Region.Proofs
