module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (CallOracle Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)

private abbrev Carried := Tuple (Val model.value) [.value word]

private abbrev carry (old : Word) : Carried := .cons old .nil

private theorem carry_eta (latched : Carried) : ∃ old : Word, carry old = latched := by
  cases latched with
  | cons old rest =>
    cases rest
    exact ⟨old, rfl⟩

variable (p : Profile)

theorem countdown_guard_ne (old delta : Word) (taken : old - delta ≠ 0) :
    countdown.guardWord old delta ≠ 0 := by
  change ofBool (old - delta != (0 : Word)) ≠ 0
  simp [ofBool]
  exact taken

theorem lower_wellFormed : p.lowerFunc.WellFormed := by
  rcases p with ⟨update, limit, guard⟩
  cases update <;> cases guard
  all_goals
    refine ⟨⟨Nat.zero_lt_succ 2, rfl, rfl⟩, ?_, ?_, rfl⟩
    · change [Reg.arg 0, .arg 1, .phi, .node 0, .node 1, .node 2, .node 3].Nodup
      decide
    · unfold Func.UsesDominated
      cbv

private theorem select_guard (b : Bool) (old : Word) (next : Carried) :
    (if b then Sum.inr next else Sum.inl old) =
      (if ofBool b = 0 then Sum.inl old else Sum.inr next) := by
  cases b <;> rfl

theorem source_step (seed delta old : Word) :
    p.graph.step model (entry seed delta) (.cons old .nil) =
      if p.guardWord old delta = 0 then .inl old else .inr (.cons (p.update.eval old delta) .nil) := by
  rcases p with ⟨update, limit, guard⟩
  cases update <;> cases guard <;> exact select_guard _ _ _

theorem incoming_operand (edge : Incoming) :
    ((p.lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, [p.incomingRegister edge]) := by
  cases edge <;> rfl

theorem latch_entry (seed delta : Word) :
    p.graph.initial model (entry seed delta) = .cons seed .nil := rfl

theorem latch_feedback (seed delta old : Word) :
    let args := appendTuple (Tuple.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
    p.graph.latch model .backedge args (p.graph.header.eval model args PUnit.unit) =
      .cons (p.update.eval old delta) .nil := by
  rcases p with ⟨update, limit, guard⟩
  cases update <;> cases guard <;> rfl

theorem transfer_incoming (edge : Incoming) (s : State Reg) (value : Word)
    (func : s.point.func = 0) (read : s.frame.get (p.incomingRegister edge) = some value) :
    transfer p.lower s 1 [p.incomingRegister edge] =
      .running ⟨⟨0, 1, 0⟩, s.frame.set .phi value, s.stack, s.mem⟩ := by
  simp [transfer, Frame.readAll, read, func]
  rfl

private theorem get_old (fr : Frame Reg) (old delta : Word)
    (hold : fr.get .phi = some old) :
    (p.headerFrame fr old delta).get .phi = some old := by
  simpa [Profile.headerFrame] using hold

private theorem get_delta (fr : Frame Reg) (old delta : Word)
    (hdelta : fr.get (.arg 1) = some delta) :
    (p.headerFrame fr old delta).get (.arg 1) = some delta := by
  simpa [Profile.headerFrame] using hdelta

/-- Successful non-call execution determines the first intermediate state. -/
private theorem ops_cons_iff {oracle : CallOracle} {op : Op Reg} {ops : List (Op Reg)}
    {fr next done : Frame Reg} {m n final : Memory}
    (exec : op.exec fr m = some (next, n)) :
    Ops.Exec oracle (op :: ops) fr m done final ↔ Ops.Exec oracle ops next n done final := by
  constructor
  · intro run
    cases run with
    | op step rest =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (step.symm.trans exec))
      exact rest
    | call => simp [Op.exec] at exec
  · exact Ops.Exec.op exec

private theorem update_eval (u : Update) (old delta : Word) :
    u.target.eval old delta = some (u.eval old delta) := by
  cases u <;> rfl

private theorem exec_update (fr : Frame Reg) (mem : Memory) (old delta : Word)
    (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta) :
    (Op.binary p.update.target (.node 0) .phi (.arg 1)).exec fr mem =
      some (fr.set (.node 0) (p.update.eval old delta), mem) := by
  simp only [Op.exec, hold, hdelta, Option.bind_some, update_eval]
  rfl

private theorem header_ops : p.header.ops =
    [Op.binary p.update.target (.node 0) .phi (.arg 1), .const (.node 1) p.limit,
      .binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)] := by
  rcases p with ⟨update, limit, guard⟩
  cases update <;> cases guard <;> rfl

theorem header_exec_iff (oracle : CallOracle) (fr done : Frame Reg) (m final : Memory)
    (old delta : Word) (hold : fr.get .phi = some old)
    (hdelta : fr.get (.arg 1) = some delta) :
    Ops.Exec oracle p.header.ops fr m done final ↔
      done = p.headerFrame fr old delta ∧ final = m := by
  let updated := fr.set (.node 0) (p.update.eval old delta)
  let withLimit := updated.set (.node 1) p.limit
  have compare :
      (Op.binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)).exec withLimit m =
        some (p.headerFrame fr old delta, m) := rfl
  rw [header_ops p, ops_cons_iff (exec_update p fr m old delta hold hdelta),
    ops_cons_iff (show (Op.const (.node 1) p.limit).exec updated m = some (withLimit, m) from rfl),
    ops_cons_iff compare]
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .nil

theorem step_entry (fr : Frame Reg) (stack : List (Activation Reg))
    (mem : Memory) (seed : Word) (read : fr.get (.arg 0) = some seed) :
    step p.lower ⟨⟨0, 0, 0⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, fr.set .phi seed, stack, mem⟩ := by
  change transfer p.lower _ 1 [p.incomingRegister .entry] = _
  exact transfer_incoming p .entry _ seed rfl read

theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg))
    (mem : Memory) (old delta : Word) (taken : p.guardWord old delta ≠ 0) :
    let after := p.headerFrame fr old delta
    step p.lower ⟨⟨0, 1, p.header.ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, after.set .phi (p.update.eval old delta), stack, mem⟩ := by
  change transfer p.lower _ (if p.guardWord old delta = 0 then 2 else 1)
    (if p.guardWord old delta = 0 then [.phi] else [p.incomingRegister .backedge]) = _
  rw [ite_eq_right taken, ite_eq_right taken]
  exact transfer_incoming p .backedge _ _ rfl rfl

private theorem exit_sound {oracle : CallOracle} {fr : Frame Reg} {mem : Memory}
    {out : Exit} {old : Word} (hold : fr.get (.node 3) = some old)
    (run : Func.Exec oracle p.lowerFunc 2 fr mem out) :
    out = .returned [old] mem := by
  cases run with
  | ret hb hops hterm hargs =>
    obtain rfl := Option.some.inj (show some exitBlock = _ from hb)
    change Ops.Exec _ [] _ _ _ _ at hops
    cases hops
    cases hterm
    have values := Option.some.inj ((by simp [Frame.readAll, hold] :
      fr.readAll [.node 3] = some [old]).symm.trans hargs)
    rw [← values]
  | jump hb _ hterm _ _ _ _ | cond hb _ hterm _ _ _ _ _ | trap hb _ hterm =>
    obtain rfl := Option.some.inj (show some exitBlock = _ from hb)
    cases hterm

private theorem header_sound {oracle : CallOracle} {l : Nat} {fr : Frame Reg} {mem : Memory}
    {out : Exit} (run : Func.Exec oracle p.lowerFunc l fr mem out) (seed delta : Word) :
    l = 1 → ∀ old : Word, fr.get .phi = some old → fr.get (.arg 1) = some delta →
      ∃ count result, p.graph.ReturnsAfter model (entry seed delta) count (.cons old .nil) result ∧
        out = .returned [result] mem := by
  induction run with
  | @cond _ _ _ _ _ _ _ _ _ _ before _ _ _ _ _ hb hops hterm hc hargs ht hw rest ih =>
    rintro rfl old hold hdelta
    obtain rfl := Option.some.inj (show some p.header = _ from hb)
    obtain ⟨rfl, rfl⟩ := (header_exec_iff p oracle _ _ _ _ old delta hold hdelta).mp hops
    change Term.cond (R := Reg) (.node 2) 1 [.node 0] 2 [.phi] = _ at hterm
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Term.cond.inj hterm
    have predicate := Option.some.inj ((rfl : (p.headerFrame before old delta).get (.node 2) =
      some (p.guardWord old delta)).symm.trans hc)
    subst_vars
    by_cases hzero : p.guardWord old delta = 0
    · simp only [ite_eq_left hzero] at hargs ht rest
      obtain rfl := Option.some.inj (show some exitBlock = _ from ht)
      have read : (p.headerFrame before old delta).readAll [.phi] = some [old] := by
        simp [Frame.readAll, get_old p before old delta hold]
      obtain rfl := Option.some.inj (read.symm.trans hargs)
      obtain rfl := Option.some.inj (show some ((p.headerFrame before old delta).set (.node 3) old) = _ from hw)
      exact ⟨0, old, .exit ((source_step p seed delta old).trans (ite_eq_left hzero)), exit_sound p rfl rest⟩
    · have hbranch := hzero
      simp only [ite_eq_right hzero] at hargs ht rest ih
      obtain rfl := Option.some.inj (show some p.header = _ from ht)
      obtain rfl := Option.some.inj ((rfl : (p.headerFrame before old delta).readAll [.node 0] =
        some [p.update.eval old delta]).symm.trans hargs)
      obtain rfl := Option.some.inj (show some ((p.headerFrame before old delta).set .phi (p.update.eval old delta)) = _ from hw)
      obtain ⟨count, result, run, returned⟩ := ih trivial (p.update.eval old delta) rfl (get_delta p before old delta hdelta)
      exact ⟨count + 1, result, .backedge ((source_step p seed delta old).trans (ite_eq_right hzero)) run, returned⟩
  | jump hb _ hterm _ _ _ _ _ | ret hb _ hterm _ | trap hb _ hterm =>
    intro hl
    subst_vars
    obtain rfl := Option.some.inj (show some p.header = _ from hb)
    cases hterm

private def entryFrame (seed delta : Word) : Frame Reg :=
  (Frame.empty.set (.arg 0) seed).set (.arg 1) delta

private theorem entry_exec_sound (oracle : CallOracle) (seed delta : Word) (mem : Memory) {out : Exit}
    (run : Func.Exec oracle p.lowerFunc 0 (entryFrame seed delta) mem out) :
    ∃ result, p.graph.Returns model (entry seed delta) result ∧ out = .returned [result] mem := by
  cases run with
  | jump hb hops hterm hargs ht hw rest =>
    obtain rfl := Option.some.inj (show some p.preheader = _ from hb)
    change Ops.Exec _ [] _ _ _ _ at hops
    cases hops
    change Term.jump (R := Reg) 1 [.arg 0] = _ at hterm
    obtain ⟨rfl, rfl⟩ := Term.jump.inj hterm
    obtain rfl := Option.some.inj ((rfl : (entryFrame seed delta).readAll [.arg 0] =
      some [seed]).symm.trans hargs)
    obtain rfl := Option.some.inj (show some p.header = _ from ht)
    obtain rfl := Option.some.inj (show some ((entryFrame seed delta).set .phi seed) = _ from hw)
    obtain ⟨count, result, run, observed⟩ := header_sound p rest seed delta rfl seed rfl rfl
    exact ⟨result, ⟨count, run⟩, observed⟩
  | cond hb _ hterm _ _ _ _ _ | ret hb _ hterm _ | trap hb _ hterm =>
    obtain rfl := Option.some.inj (show some p.preheader = _ from hb)
    cases hterm

/-- Prepend the actual header operations to a counted machine suffix. -/
private theorem header_steps (fr : Frame Reg) (mem : Memory) (old delta : Word)
    (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta)
    {n : Nat} {finish : State Reg}
    (tail : StepsNWithin p.lower [] n
      ⟨⟨0, 1, p.header.ops.length⟩, p.headerFrame fr old delta, [], mem⟩ finish) :
    StepsNWithin p.lower [] (n + 3) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ finish := by
  let updated := fr.set (.node 0) (p.update.eval old delta)
  let withLimit := updated.set (.node 1) p.limit
  have block : p.lower.block? 0 1 = some p.header := rfl
  have fetchUpdate : p.header.ops[0]? = some (.binary p.update.target (.node 0) .phi (.arg 1)) := by
    rw [header_ops p]
    rfl
  have fetchLimit : p.header.ops[1]? = some (.const (.node 1) p.limit) := by
    rw [header_ops p]
    rfl
  have fetchGuard :
      p.header.ops[2]? = some (.binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)) := by
    rw [header_ops p]
    rfl
  have first := Transition.op (s := (⟨⟨0, 1, 0⟩, fr, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchUpdate) (exec_update p fr mem old delta hold hdelta)
  have second := Transition.op (s := (⟨⟨0, 1, 1⟩, updated, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchLimit) (rfl :
      (Op.const (.node 1) p.limit).exec updated mem = some (withLimit, mem))
  have third := Transition.op (s := (⟨⟨0, 1, 2⟩, withLimit, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchGuard) (rfl :
      (Op.binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)).exec withLimit mem =
        some (p.headerFrame fr old delta, mem))
  have length : p.header.ops.length = 3 := by rw [header_ops p]; rfl
  rw [length] at tail
  exact .head ⟨first.step_eq, List.nil_suffix⟩
    (.head ⟨second.step_eq, List.nil_suffix⟩ (.head ⟨third.step_eq, List.nil_suffix⟩ tail))

private theorem exit_step (fr : Frame Reg) (mem : Memory) (old delta : Word)
    (hold : fr.get .phi = some old) (hzero : p.guardWord old delta = 0) :
    let after := p.headerFrame fr old delta
    step p.lower ⟨⟨0, 1, p.header.ops.length⟩, after, [], mem⟩ =
      .running ⟨⟨0, 2, 0⟩, after.set (.node 3) old, [], mem⟩ := by
  change transfer p.lower _ (if p.guardWord old delta = 0 then 2 else 1)
    (if p.guardWord old delta = 0 then [.phi] else [.node 0]) = _
  rw [ite_eq_left hzero, ite_eq_left hzero]
  simp [transfer, Frame.readAll, get_old p fr old delta hold]
  rfl

theorem header_activation (fr : Frame Reg) (mem : Memory) (old delta : Word)
    (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta) :
    let after := p.headerFrame fr old delta
    StepsNWithin p.lower [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (if p.guardWord old delta = 0 then ⟨⟨0, 2, 0⟩, after.set (.node 3) old, [], mem⟩
       else ⟨⟨0, 1, 0⟩, after.set .phi (p.update.eval old delta), [], mem⟩) := by
  by_cases halt : p.guardWord old delta = 0
  · simp only [ite_eq_left halt]
    exact header_steps p fr mem old delta hold hdelta
      (.head ⟨exit_step p fr mem old delta hold halt, List.nil_suffix⟩ .refl)
  · simp only [ite_eq_right halt]
    exact header_steps p fr mem old delta hold hdelta
      (.head ⟨step_feedback p fr [] mem old delta halt, List.nil_suffix⟩ .refl)

private theorem counted_header (seed delta : Word) (mem : Memory) {count : Nat}
    {latched : Carried} {result : sortValue model.value word}
    (run : p.graph.ReturnsAfter model (entry seed delta) count latched result) :
    ∀ fr : Frame Reg, fr.get .phi = some (latched.get .head) → fr.get (.arg 1) = some delta →
      ∃ finish, StepsNWithin p.lower [] (4 * (count + 1)) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ finish ∧
        step p.lower finish = .returned [result] mem := by
  refine Graph.ReturnsAfter.rec (g := p.graph) (m := model) (input := entry seed delta)
    (motive := fun count latched result _ =>
      ∀ fr : Frame Reg, fr.get .phi = some (latched.get .head) → fr.get (.arg 1) = some delta →
        ∃ finish, StepsNWithin p.lower [] (4 * (count + 1)) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ finish ∧
          step p.lower finish = .returned [result] mem) ?_ ?_ run
  · intro latched result taken fr hold hdelta
    obtain ⟨old, rfl⟩ := carry_eta latched
    have taken := (source_step p seed delta old).symm.trans taken
    have hzero : p.guardWord old delta = 0 := by
      by_contra ne
      rw [ite_eq_right ne] at taken
      cases taken
    have value := Sum.inl.inj ((ite_eq_left hzero).symm.trans taken)
    let finish : State Reg := ⟨⟨0, 2, 0⟩, (p.headerFrame fr old delta).set (.node 3) old, [], mem⟩
    refine ⟨finish, header_steps p fr mem old delta hold hdelta
      (.head ⟨exit_step p fr mem old delta hold hzero, List.nil_suffix⟩ .refl), ?_⟩
    rw [← value]
    rfl
  · intro count latched next _ taken _ ih fr hold hdelta
    obtain ⟨old, rfl⟩ := carry_eta latched
    have taken := (source_step p seed delta old).symm.trans taken
    have hne : p.guardWord old delta ≠ 0 := by
      intro zero
      rw [ite_eq_left zero] at taken
      cases taken
    obtain rfl := Sum.inr.inj ((ite_eq_right hne).symm.trans taken)
    obtain ⟨finish, rest, observed⟩ := ih
      ((p.headerFrame fr old delta).set .phi (p.update.eval old delta)) rfl (get_delta p fr old delta hdelta)
    exact ⟨finish, header_steps p fr mem old delta hold hdelta
      (.head ⟨step_feedback p fr [] mem old delta hne, List.nil_suffix⟩ rest), observed⟩

private theorem counted_entry (seed delta : Word) (mem : Memory) (count : Nat) (value : Word)
    (source : p.graph.ReturnsAfter model (entry seed delta) count (p.graph.initial model (entry seed delta)) value) :
    ∃ start finish, p.lower.start 0 [seed, delta] mem = some start ∧
      StepsNWithin p.lower [] (4 * count + 5) start finish ∧ step p.lower finish = .returned [value] mem := by
  obtain ⟨finish, steps, observed⟩ :=
    counted_header p seed delta mem source ((entryFrame seed delta).set .phi seed) rfl rfl
  have entered := step_entry p (entryFrame seed delta) [] mem seed rfl
  refine ⟨⟨⟨0, 0, 0⟩, entryFrame seed delta, [], mem⟩, finish, rfl, ?_, observed⟩
  exact .head ⟨entered, List.nil_suffix⟩ steps

theorem lower_returns_iff (seed delta : Word) (initial final : Memory) (returned : List Word) :
    p.lower.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, p.graph.Returns model (entry seed delta) value ∧
        returned = [value] ∧ final = initial := by
  constructor
  · intro oracle
    have bridge :
        Func.Exec p.lower.oracle p.lowerFunc 0 (entryFrame seed delta) initial (.returned returned final) ↔
          p.lower.oracle 0 [seed, delta] initial returned final :=
      Func.exec_returned_iff_oracle (p := p.lower) (f := 0) (fn := p.lowerFunc)
        (b := p.preheader) rfl rfl rfl
    obtain ⟨value, source, observed⟩ := entry_exec_sound p p.lower.oracle seed delta initial (bridge.mpr oracle)
    obtain ⟨valuesEq, memEq⟩ := Exit.returned.inj observed
    exact ⟨value, source, valuesEq, memEq⟩
  · rintro ⟨value, ⟨count, source⟩, valuesEq, memEq⟩
    subst returned
    subst final
    obtain ⟨start, finish, started, steps, observed⟩ := counted_entry p seed delta initial count value source
    exact ⟨start, started, finish, stepsWithin_nil_iff.mp steps.toStepsWithin, observed⟩

private theorem return_length_unique {prog : Prog Reg} {n j : Nat} {s a b : State Reg}
    {vs : List Word} {mem : Memory}
    (left : StepsNWithin prog [] n s a) (leftRet : step prog a = .returned vs mem)
    (right : StepsNWithin prog [] j s b) (rightRet : step prog b = .returned vs mem) :
    n = j := by
  induction left generalizing j b with
  | refl =>
    cases right with
    | refl => rfl
    | head next _ => cases leftRet.symm.trans next.1
  | head next _ ih =>
    cases right with
    | refl => cases rightRet.symm.trans next.1
    | head other rest =>
      cases Step.deterministic next.1 other.1
      exact congrArg Nat.succ (ih leftRet rest rightRet)

theorem lower_stepsN_iff (seed delta : Word) (initial final : Memory) (returned : List Word) (backedges : Nat) :
    (∃ start finish, p.lower.start 0 [seed, delta] initial = some start ∧
      StepsNWithin p.lower [] (4 * backedges + 5) start finish ∧
        step p.lower finish = .returned returned final) ↔
    ∃ value : Word, p.graph.ReturnsAfter model (entry seed delta) backedges
      (p.graph.initial model (entry seed delta)) value ∧ returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, finish, started, steps, observed⟩
    have oracle : p.lower.oracle 0 [seed, delta] initial returned final :=
      ⟨start, started, finish, stepsWithin_nil_iff.mp steps.toStepsWithin, observed⟩
    obtain ⟨value, ⟨count, source⟩, valuesEq, memEq⟩ :=
      (lower_returns_iff p seed delta initial final returned).mp oracle
    subst returned
    subst final
    obtain ⟨start', finish', started', steps', observed'⟩ := counted_entry p seed delta initial count value source
    obtain rfl := Option.some.inj (started'.symm.trans started)
    have counts := return_length_unique steps observed steps' observed'
    have : backedges = count := by omega
    subst backedges
    exact ⟨value, source, rfl, rfl⟩
  · rintro ⟨value, source, valuesEq, memEq⟩
    subst returned
    subst final
    exact counted_entry p seed delta initial backedges value source

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Proofs
