module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple)
open Silmaril.SSA.RVSDG (Tuple)

theorem recognize_eq_some_iff (g : Native) (p : Profile) :
    recognize g = some p ↔ g = graph p := by
  constructor
  · intro ok
    cases decoded : Checked.decodeSchedule g.header with
    | none => simp [recognize, decoded] at ok
    | some candidate =>
      simp only [recognize, decoded, Option.bind_some] at ok
      split at ok
      · rename_i agree
        obtain rfl := Option.some.inj ok
        apply Checked.graph_eq_of_provenance _ agree
        exact Checked.schedule_eq g.header candidate updateWires guardWires decoded
          (congrArg Checked.Provenance.producers agree)
      · cases ok
  · rintro rfl
    have decoded : Checked.decodeSchedule (graph p).header = some p :=
      Checked.decode_schedule p updateWires guardWires
    simp [recognize, decoded]

private theorem exists_pair (values : WordTuple 2) : ∃ a b, values = pair a b := by
  cases values with
  | cons a rest =>
    cases rest with
    | cons b tail =>
      cases tail
      exact ⟨a, b, rfl⟩

theorem feedback_latch (p : Profile) (input : WordTuple 2) (first second : Word) :
    let args := appendTuple (pair first second) input
    (graph p).latch model .backedge args ((graph p).header.eval model args PUnit.unit) =
      pair (p.update.eval first second) first := by
  obtain ⟨a, b, rfl⟩ := exists_pair input
  rcases p with ⟨update, limit, cmp⟩
  cases update <;> cases cmp <;> rfl

private theorem selectGuard (test : Bool) (exit : Word) (next : WordTuple 2) :
    (if test then Sum.inr next else Sum.inl exit) =
      (if ofBool test = 0 then Sum.inl exit else Sum.inr next) := by
  cases test <;> rfl

theorem native_step (p : Profile) (input : WordTuple 2) (first second : Word) :
    (graph p).step model input (pair first second) =
      if p.guardWord first second = 0 then .inl second else .inr (pair (p.update.eval first second) first) := by
  obtain ⟨a, b, rfl⟩ := exists_pair input
  rcases p with ⟨update, limit, cmp⟩
  cases update <;> cases cmp <;> exact selectGuard _ _ _

private theorem branch (p : Profile) (fr : Frame Reg) (first second : Word) (mem : Memory)
    (hfirst : fr.get (.arg 2) = some first) (hsecond : fr.get (.arg 3) = some second) :
    step (rtl (graph p)) ⟨⟨0, 1, (bankHeader (graph p)).ops.length⟩, p.headerFrame fr first second, [], mem⟩ =
      .running (successor p fr first second mem) := by
  let after := p.headerFrame fr first second
  have readFirst : after.get (.arg 2) = some first := by simpa [after, Profile.headerFrame] using hfirst
  have readSecond : after.get (.arg 3) = some second := by simpa [after, Profile.headerFrame] using hsecond
  have bound : (rtl (graph p)).block? 0 2 = some exitBlock := rfl
  have term : (bankHeader (graph p)).term = .cond (.node 2) 1 [.node 0, .arg 2] 2 [.arg 3] := rfl
  have fetch := Prog.fetch_term (p := rtl (graph p)) (f := 0) (l := 1)
    (b := bankHeader (graph p)) rfl
  simp only [step, fetch, term]
  change transfer (rtl (graph p)) ⟨⟨0, 1, (bankHeader (graph p)).ops.length⟩, after, [], mem⟩
    (if p.guardWord first second = 0 then 2 else 1)
    (if p.guardWord first second = 0 then [.arg 3] else [.node 0, .arg 2]) = _
  by_cases halt : p.guardWord first second = 0
  · rw [ite_eq_left halt, ite_eq_left halt]
    simp [transfer, Frame.readAll, readSecond, bound, exitBlock, Frame.writeAll, successor, halt]
    rfl
  · rw [ite_eq_right halt, ite_eq_right halt]
    have computed : after.get (.node 0) = some (p.update.eval first second) := rfl
    have readOld : after.readAll [.node 0, .arg 2] = some (words (pair (p.update.eval first second) first)) := by
      change after.readAll [.node 0, .arg 2] = some [p.update.eval first second, first]
      simp [Frame.readAll, computed, readFirst]
    rw [successor, ite_eq_right halt]
    exact transfer_bank (graph p) _ _ _ rfl readOld

private theorem header_ops (p : Profile) :
    (bankHeader (graph p)).ops =
      [.binary p.update.target (.node 0) (.arg 2) (.arg 3), .const (.node 1) p.limit,
       .binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)] := by
  rcases p with ⟨update, limit, cmp⟩
  cases update <;> cases cmp <;> rfl

theorem header_activation (p : Profile) (fr : Frame Reg) (first second : Word) (mem : Memory)
    (hfirst : fr.get (.arg 2) = some first) (hsecond : fr.get (.arg 3) = some second) :
    StepsNWithin (rtl (graph p)) [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (successor p fr first second mem) := by
  let updated := fr.set (.node 0) (p.update.eval first second)
  let withLimit := updated.set (.node 1) p.limit
  have block : (rtl (graph p)).block? 0 1 = some (bankHeader (graph p)) := rfl
  have fetchUpdate : (bankHeader (graph p)).ops[0]? =
      some (.binary p.update.target (.node 0) (.arg 2) (.arg 3)) := by rw [header_ops]; rfl
  have fetchLimit : (bankHeader (graph p)).ops[1]? = some (.const (.node 1) p.limit) := by
    rw [header_ops]; rfl
  have fetchGuard : (bankHeader (graph p)).ops[2]? =
      some (.binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)) := by rw [header_ops]; rfl
  have runUpdate : (Op.binary p.update.target (.node 0) (.arg 2) (.arg 3)).exec fr mem =
      some (updated, mem) := by
    simp only [Op.exec, hfirst, hsecond]
    rcases p with ⟨update, limit, cmp⟩
    cases update <;> rfl
  have firstStep := Transition.op (s := (⟨⟨0, 1, 0⟩, fr, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchUpdate) runUpdate
  have secondStep := Transition.op (s := (⟨⟨0, 1, 1⟩, updated, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchLimit) (rfl : (Op.const (.node 1) p.limit).exec updated mem = some (withLimit, mem))
  have thirdStep := Transition.op (s := (⟨⟨0, 1, 2⟩, withLimit, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchGuard) (rfl : (Op.binary (.cmp p.guard.target) (.node 2) (.node 0) (.node 1)).exec
      withLimit mem = some (p.headerFrame fr first second, mem))
  have length : (bankHeader (graph p)).ops.length = 3 := by rw [header_ops]; rfl
  have branchStep := branch p fr first second mem hfirst hsecond
  rw [length] at branchStep
  exact .head ⟨firstStep.step_eq, List.nil_suffix⟩ (.head ⟨secondStep.step_eq, List.nil_suffix⟩
    (.head ⟨thirdStep.step_eq, List.nil_suffix⟩ (.head ⟨branchStep, by unfold successor; split <;> exact List.nil_suffix⟩ .refl)))

private theorem source_returns (p : Profile) (input : WordTuple 2) (mem : Memory)
    {count : Nat} {old : WordTuple 2} {value : Word}
    (source : (graph p).ReturnsAfter model input count old value) :
    ∀ fr : Frame Reg, fr.get (.arg 2) = some (old.get .head) →
      fr.get (.arg 3) = some (old.get (.tail .head)) →
      Behaves (rtl (graph p)) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (.returned [value] mem) := by
  refine Graph.ReturnsAfter.rec (g := graph p) (m := model) (input := input)
    (motive := fun _ old value _ => ∀ fr, fr.get (.arg 2) = some (old.get .head) →
      fr.get (.arg 3) = some (old.get (.tail .head)) →
      Behaves (rtl (graph p)) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (.returned [value] mem)) ?_ ?_ source
  · intro old value selected fr hfirst hsecond
    obtain ⟨a, b, rfl⟩ := exists_pair old
    rw [native_step] at selected
    by_cases halt : p.guardWord a b = 0
    · rw [ite_eq_left halt] at selected
      obtain rfl := Sum.inl.inj selected
      have activated := header_activation p fr a b mem hfirst hsecond
      rw [successor, ite_eq_left halt] at activated
      exact ⟨_, activated.toStepsWithin.toSteps, rfl⟩
    · rw [ite_eq_right halt] at selected
      cases selected
  · intro _ old next value selected _ ih fr hfirst hsecond
    obtain ⟨a, b, rfl⟩ := exists_pair old
    rw [native_step] at selected
    by_cases halt : p.guardWord a b = 0
    · rw [ite_eq_left halt] at selected
      cases selected
    · rw [ite_eq_right halt] at selected
      obtain rfl := Sum.inr.inj selected
      have activated := header_activation p fr a b mem hfirst hsecond
      rw [successor, ite_eq_right halt] at activated
      obtain ⟨finish, suffix, observed⟩ := ih
        (bindBank (p.headerFrame fr a b) (pair (p.update.eval a b) a)) rfl rfl
      exact ⟨finish, activated.toStepsWithin.toSteps.trans suffix, observed⟩

private theorem machine_returns (p : Profile) (input : WordTuple 2) (mem final : Memory)
    (returned : List Word) (fuel : Nat) (fr : Frame Reg) (a b : Word)
    (hfirst : fr.get (.arg 2) = some a) (hsecond : fr.get (.arg 3) = some b)
    (observed : run (rtl (graph p)) fuel ⟨⟨0, 1, 0⟩, fr, [], mem⟩ = .returned returned final) :
    ∃ count value, (graph p).ReturnsAfter model input count (pair a b) value ∧
      returned = [value] ∧ final = mem := by
  induction fuel using Nat.strongRecOn generalizing fr a b with
  | ind fuel ih =>
    obtain ⟨remaining, length, result⟩ :=
      run_after_prefix (header_activation p fr a b mem hfirst hsecond) observed
    by_cases halt : p.guardWord a b = 0
    · rw [successor, ite_eq_left halt] at result
      cases remaining with
      | zero => cases result
      | succ remaining =>
        have exactly : Result.returned [b] mem = (.returned returned final : Result Reg) := result
        obtain ⟨rfl, rfl⟩ := Result.returned.inj exactly
        exact ⟨0, b, .exit ((native_step p input a b).trans (ite_eq_left halt)), rfl, rfl⟩
    · rw [successor, ite_eq_right halt] at result
      obtain ⟨count, value, source, same, memory⟩ := ih remaining (by omega)
        (bindBank (p.headerFrame fr a b) (pair (p.update.eval a b) a)) (p.update.eval a b) a rfl rfl result
      exact ⟨count + 1, value, .backedge ((native_step p input a b).trans (ite_eq_right halt)) source,
        same, memory⟩

theorem rtl_returns_iff (p : Profile) (input : WordTuple 2) (initial final : Memory)
    (returned : List Word) :
    (rtl (graph p)).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (graph p).Returns model input value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨a, b, rfl⟩ := exists_pair input
  let fr := bindWords 0 Frame.empty (pair a b)
  let initialState : State Reg := ⟨⟨0, 0, 0⟩, fr, [], initial⟩
  let entered : State Reg := ⟨⟨0, 1, 0⟩, bindBank fr (pair a b), [], initial⟩
  have started : (rtl (graph p)).start 0 (words (pair a b)) initial = some initialState := rfl
  have entryStep : step (rtl (graph p)) initialState = .running entered := rfl
  constructor
  · rintro ⟨start, hstart, finish, path, observed⟩
    obtain rfl := Option.some.inj (hstart.symm.trans started)
    obtain ⟨fuel, run⟩ := fuel_of_steps path observed
    cases fuel with
    | zero => cases run
    | succ fuel =>
      have rest : RTL.SSA.run (rtl (graph p)) fuel entered = .returned returned final := by
        simpa only [RTL.SSA.run, entryStep] using run
      obtain ⟨count, value, source, same, memory⟩ :=
        machine_returns p (pair a b) initial final returned fuel _ a b rfl rfl rest
      exact ⟨value, ⟨count, source⟩, same, memory⟩
  · rintro ⟨value, ⟨count, source⟩, rfl, memory⟩
    subst final
    obtain ⟨finish, suffix, observed⟩ := source_returns p (pair a b) initial source
      (bindBank fr (pair a b)) rfl rfl
    exact ⟨initialState, started, finish, .head entryStep suffix, observed⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Proofs
