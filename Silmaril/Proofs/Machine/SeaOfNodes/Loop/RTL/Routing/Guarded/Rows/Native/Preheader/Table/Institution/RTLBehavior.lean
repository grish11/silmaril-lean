module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Defs
public import Silmaril.Logic.Institution.Observational.Sentence
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Satisfaction

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.Logic.Institution.Observational (Sentence)

variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable {left : SourceWithEntry arity entrySigs sigs} {right : SourceWithEntry arity rightEntry rightSigs}
variable {leftTargets rightTargets : Checked.Phi.Targets}

private theorem plan_start (p : Plan arity entrySigs) (input : WordTuple arity) (initial : Memory) :
    p.rtl.start 0 (words input) initial = some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], initial⟩ := by
  change ((Frame.empty.writeAll (paramRegs 0 arity) (words input)).map
    (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
    (fun entered => (⟨entered.1, entered.2, [], initial⟩ : State Reg)) = _
  rw [bindWords_write]
  rfl

theorem rtl_start_exists (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    ∃ start, leftTargets.1.start 0 (words input) initial = some start := by
  obtain ⟨p, _, _, rfl⟩ := lowerChecked_sound accepted
  exact ⟨_, plan_start p input initial⟩

private theorem plan_diverges_of_absent (p : Plan arity entrySigs) (input : WordTuple arity)
    (initial : Memory) (absent : p.graph.denote model input = Part.none) :
    p.rtl.divOracle 0 (words input) initial := by
  let header (s : State Reg) := ∃ (fr : Frame Reg) (bank : WordTuple arity),
    s = ⟨⟨0, 1, 0⟩, fr, [], initial⟩ ∧ ArgsMatch fr (appendTuple bank input) ∧
      ∀ count value, ¬ p.graph.ReturnsAfter model input count bank value
  have backedge (s : State Reg) (atHeader : header s) :
      ∃ n t, StepsNWithin p.rtl [] (n + 1) s t ∧ header t := by
    obtain ⟨fr, bank, rfl, agree, noReturn⟩ := atHeader
    have packet := header_packet p input bank fr initial agree
    cases branch : p.graph.step model input bank with
    | inl value => exact (noReturn 0 value (.exit branch)).elim
    | inr next =>
      rw [branch] at packet
      exact ⟨p.row.compareIndex + 1, _, packet.1, _, next, rfl, packet.2.1,
        fun count value run => noReturn (count + 1) value (.backedge branch run)⟩
  obtain ⟨fr, entry, agree, _⟩ := entry_packet p input _ initial (bindWords_args input)
  have initialHeader : header ⟨⟨0, 1, 0⟩, fr, [], initial⟩ := by
    refine ⟨fr, p.graph.initial model input, rfl, agree, fun count value run => ?_⟩
    exact (Part.eq_none_iff'.mp absent) (Part.dom_iff_mem.mpr
      ⟨value, (p.graph.returns_iff_mem_denote model input value).mp ⟨count, run⟩⟩)
  -- Include states partway through the entry or an activation. At a header
  -- the next backedge supplies at least one instruction before the next header.
  let pending (s : State Reg) := ∃ n t, StepsNWithin p.rtl [] n s t ∧ header t
  refine ⟨_, plan_start p input initial, InfiniteTrace.coinduct pending ?_ ⟨_, _, entry, initialHeader⟩⟩
  rintro s ⟨n, t, path, atHeader⟩
  cases path with
  | head first rest => exact ⟨_, first.1, _, _, rest, atHeader⟩
  | refl =>
    obtain ⟨_, _, next, newHeader⟩ := backedge s atHeader
    cases next with
    | head first rest => exact ⟨_, first.1, _, _, rest, newHeader⟩

private theorem rtl_behavior_unique {target : Prog Reg} {input : WordTuple arity} {initial : Memory}
    {a b : Behavior} (observed : a ∈ rtlBehaviors input initial target)
    (other : b ∈ rtlBehaviors input initial target) : a = b := by
  obtain ⟨start, starts, run⟩ := observed
  obtain ⟨otherStart, startsOther, runOther⟩ := other
  cases Option.some.inj (starts.symm.trans startsOther)
  exact Behaves.unique run runOther

theorem rtl_divOracle_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    leftTargets.1.divOracle 0 (words input) initial ↔ left.denote model input = Part.none := by
  constructor
  · intro infinite
    apply Part.eq_none_iff'.mpr
    intro defined
    obtain ⟨value, present⟩ := Part.dom_iff_mem.mp defined
    have returns := (left.returns_iff_mem_denote model input value).mpr present
    have finite := (rtl_return_iff accepted input initial initial [value]).mpr ⟨value, returns, rfl, rfl⟩
    cases rtl_behavior_unique (a := .diverges) (b := .returned [value] initial) infinite finite
  · intro absent
    obtain ⟨p, recognized, _, rfl⟩ := lowerChecked_sound accepted
    obtain ⟨rfl, rfl⟩ := recognize_sound recognized
    exact plan_diverges_of_absent p input initial absent

theorem rtl_behavior_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) (outcome : Behavior) :
    outcome ∈ rtlBehaviors input initial leftTargets.1 ↔
      match outcome with
      | .returned values final =>
        ∃ value : Word, value ∈ left.denote model input ∧ values = [value] ∧ final = initial
      | .diverges => left.denote model input = Part.none
      | .trapped _ | .stuck => False := by
  have noFault {fault : Behavior} (noReturn : ∀ vs m, fault ≠ .returned vs m)
      (noDiverge : fault ≠ .diverges) : fault ∉ rtlBehaviors input initial leftTargets.1 := by
    intro failed
    classical
    by_cases defined : (left.denote model input).Dom
    · obtain ⟨value, present⟩ := Part.dom_iff_mem.mp defined
      have returns := (left.returns_iff_mem_denote model input value).mpr present
      have finite := (rtl_return_iff accepted input initial initial [value]).mpr ⟨value, returns, rfl, rfl⟩
      exact noReturn _ _ (rtl_behavior_unique failed finite)
    · have infinite := (rtl_divOracle_iff accepted input initial).mpr (Part.eq_none_iff'.mpr defined)
      exact noDiverge (rtl_behavior_unique failed infinite)
  cases outcome with
  | returned values final =>
    exact (rtl_return_iff accepted input initial final values).trans
      (exists_congr fun value => and_congr (left.returns_iff_mem_denote model input value) Iff.rfl)
  | diverges => exact rtl_divOracle_iff accepted input initial
  | trapped _ => exact iff_false_intro (noFault (by simp) (by simp))
  | stuck => exact iff_false_intro (noFault (by simp) (by simp))

theorem rtl_equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (input : WordTuple arity) (initial : Memory) :
    (Sentence.eq leftTargets.1 rightTargets.1).Holds (rtlBehaviors input initial) ↔
      left.denote model input = right.denote model input := by
  change rtlBehaviors input initial leftTargets.1 = rtlBehaviors input initial rightTargets.1 ↔ _
  constructor
  · intro agree
    apply (equation_at_iff leftChecked rightChecked input initial).1.mp
    ext ⟨value, final⟩
    exact Set.ext_iff.mp agree (Behavior.returned [value] final)
  · intro agree
    ext outcome
    rw [rtl_behavior_iff leftChecked, rtl_behavior_iff rightChecked, agree]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs
