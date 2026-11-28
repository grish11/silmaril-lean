module

public import Silmaril.Machine.PEG.CountedLoop.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Thms

public section

namespace Silmaril.Machine.PEG.CountedLoop.Proofs

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Code Eval OpSignature i1)
open Silmaril.MLIR.SCF (While Condition Yield Return)

set_option backward.isDefEq.respectTransparency false

/-- The same frame as three successful writes to one block's parameter bank. -/
private def bindBank (reg : Nat → Register) (fr : Frame Register) (count left right : Word) :
    Frame Register :=
  ((fr.set (reg 0) count).set (reg 1) left).set (reg 2) right

private def initialFrame (count left right : Word) : Frame Register :=
  bindBank .input .empty count left right

private def atBlock (label : Nat) (fr : Frame Register) (mem : Memory) : State Register :=
  ⟨⟨0, label, 0⟩, fr, [], mem⟩

private def beforeState (fr : Frame Register) (mem : Memory) (count left right : Word) :
    State Register :=
  atBlock 1 (bindBank .before fr count left right) mem

private def afterState (fr : Frame Register) (mem : Memory) (count left right : Word) :
    State Register :=
  atBlock 2 (bindBank .after (bindBank .before fr count left right) count left right) mem

private def exitState (fr : Frame Register) (mem : Memory) (left right : Word) : State Register :=
  atBlock 3 (bindBank .exit (bindBank .before fr 0 left right) 0 left right) mem

private def updatedFrame (fr : Frame Register) (count left right : Word) : Frame Register :=
  ((bindBank .after (bindBank .before fr count left right) count left right).set .nextCount
    (count - 1)).set .nextRight
    (left + right)

private theorem start_eq (mem : Memory) (count left right : Word) :
    program.start 0 (words (bank count left right)) mem =
      some (atBlock 0 (initialFrame count left right) mem) := rfl

private theorem preheader_steps (fuel : Nat) (mem : Memory) (count left right : Word) :
    run program (fuel + 2) (atBlock 0 (initialFrame count left right) mem) =
      run program fuel (beforeState ((initialFrame count left right).set .one 1) mem count left right) :=
  rfl

private theorem header_exit (fr : Frame Register) (mem : Memory) (left right : Word) :
    step program (beforeState fr mem 0 left right) = .running (exitState fr mem left right) := rfl

private theorem header_continue (fr : Frame Register) (mem : Memory) (count left right : Word)
    (continues : count ≠ 0) :
    step program (beforeState fr mem count left right) = .running (afterState fr mem count left right) := by
  change transfer program (beforeState fr mem count left right)
    (if count = 0 then 3 else 2) _ = _
  simp only [ite_eq_right continues]; rfl

private theorem exit_step (fr : Frame Register) (mem : Memory) (left right : Word) :
    step program (exitState fr mem left right) = .returned [0, left, right] mem := rfl

private theorem updated_one (fr : Frame Register) (count left right : Word) :
    (updatedFrame fr count left right).get .one = fr.get .one := rfl

private theorem latch_steps (fuel : Nat) (fr : Frame Register) (mem : Memory)
    (count left right : Word) (one : fr.get .one = some 1) :
    run program (fuel + 3) (afterState fr mem count left right) =
      run program fuel (beforeState (updatedFrame fr count left right) mem (count - 1) right (left + right)) := by
  let state := afterState fr mem count left right
  have first : step program state =
      .running ⟨⟨0, 2, 1⟩, state.frame.set .nextCount (count - 1), [], mem⟩ := by
    have fetched : program.fetch state.point =
        some (.op (.binary .sub .nextCount (.after 0) .one)) := rfl
    have counter : state.frame.get (.after 0) = some count := rfl
    have constant : state.frame.get .one = some 1 := one
    have executed : (Op.binary .sub Register.nextCount (.after 0) .one).exec state.frame mem =
        some (state.frame.set .nextCount (count - 1), mem) := by
      rw [Op.exec, counter, constant]
      rfl
    exact (Transition.op (s := state) fetched executed).step_eq
  rw [run, first]
  rfl

private def returned (result : Result Register) : Option (List Word × Memory) :=
  match result with
  | .returned values mem => some (values, mem)
  | _ => none

private theorem returned_eq {result : Result Register} {values : List Word} {mem : Memory} :
    returned result = some (values, mem) ↔ result = .returned values mem := by
  cases result <;> simp [returned]

variable {Op : OpSignature}
variable (nonzero : Op [i64] i1) (pred : Op [i64] i64) (add : Op [i64, i64] i64) (evalOp : Eval Op)
variable (nz : ∀ c : Word, (evalOp nonzero (.cons c .nil)).getLsbD 0 = (c != 0))
variable (dec : ∀ c : Word, evalOp pred (.cons c .nil) = c - 1)
variable (sum : ∀ x y : Word, evalOp add (.cons x (.cons y .nil)) = x + y)

include nz dec sum in
private theorem source_tick (fuel : Nat) (input : Env Bank) (count left right : Word) :
    (source nonzero pred add).runFrom evalOp input (fuel + 1) (bank count left right) =
      if count = 0 then some (bank count left right)
      else (source nonzero pred add).runFrom evalOp input fuel (bank (count - 1) right (left + right)) := by
  rw [While.runFrom]
  change (if (evalOp nonzero (.cons count .nil)).getLsbD 0 then
    (source nonzero pred add).runFrom evalOp input fuel
      (bank (evalOp pred (.cons count .nil)) right (evalOp add (.cons left (.cons right .nil))))
    else some (bank count left right)) = _
  rw [nz, dec, sum]
  by_cases stopped : count = 0
  · subst count
    rfl
  · have continuing : (count != (0 : Word)) = true := bne_iff_ne.mpr stopped
    rw [continuing, ite_eq_left rfl, ite_eq_right stopped]

include nz dec sum in
private theorem runs_aligned (fuel : Nat) (input : Env Bank) (fr : Frame Register) (mem : Memory)
    (count left right : Word) (one : fr.get .one = some 1) :
    returned (run program (4 * fuel) (beforeState fr mem count left right)) =
      ((source nonzero pred add).runFrom evalOp input fuel (bank count left right)).map
        (fun result => (words result, mem)) := by
  induction fuel generalizing fr count left right with
  | zero => rfl
  | succ fuel ih =>
    rw [source_tick nonzero pred add evalOp nz dec sum]
    rw [show 4 * (fuel + 1) = (4 * fuel + 3) + 1 by omega, run]
    by_cases stopped : count = 0
    · subst count
      rw [header_exit, ite_eq_left rfl]
      change returned (run program ((4 * fuel + 2) + 1) (exitState fr mem left right)) = _
      rw [run, exit_step]
      rfl
    · rw [header_continue _ _ _ _ _ stopped, ite_eq_right stopped]
      change returned (run program (4 * fuel + 3) (afterState fr mem count left right)) = _
      rw [latch_steps _ _ _ _ _ _ one]
      exact ih _ _ _ _ ((updated_one fr count left right).trans one)

private theorem bank_cases : ∀ input : Env Bank, ∃ count left right, input = bank count left right
  | .cons count (.cons left (.cons right .nil)) => ⟨count, left, right, rfl⟩

include nz dec sum in
private theorem main_aligned (fuel : Nat) (input : Env Bank) (mem : Memory) :
    returned (program.runMain (4 * fuel + 2) 0 (words input) mem) =
      ((source nonzero pred add).run evalOp fuel input).map (fun result => (words result, mem)) := by
  obtain ⟨count, left, right, rfl⟩ := bank_cases input
  rw [Prog.runMain, start_eq]
  change returned (run program (4 * fuel + 2) (atBlock 0 (initialFrame count left right) mem)) = _
  rw [preheader_steps]
  exact runs_aligned nonzero pred add evalOp nz dec sum fuel _ _ _ _ _ _ rfl

private theorem runs_mono (p : Prog Register) (s : State Register) (fuel extra : Nat)
    (values : List Word) (mem : Memory) (ran : run p fuel s = .returned values mem) :
    run p (fuel + extra) s = .returned values mem := by
  induction fuel generalizing s with
  | zero => cases ran
  | succ fuel ih =>
    rw [run] at ran
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, run]
    cases next : step p s with
    | running target => exact ih target (by simpa only [next] using ran)
    | returned _ _ => simpa only [next] using ran
    | trapped _ => simp [next] at ran
    | stuck => simp [next] at ran

private theorem main_mono (fuel more : Nat) (le : fuel ≤ more)
    (input : Env Bank) (initial final : Memory) (values : List Word)
    (ran : program.runMain fuel 0 (words input) initial = .returned values final) :
    program.runMain more 0 (words input) initial = .returned values final := by
  unfold Prog.runMain at *
  cases start : program.start 0 (words input) initial with
  | none => simp [start] at ran
  | some state =>
    simp only [start] at ran ⊢
    rw [show more = fuel + (more - fuel) by omega]
    exact runs_mono _ _ _ _ _ _ ran

include nz dec sum in
theorem returns_iff (input : Env Bank) (initial final : Memory) (values : List Word) :
    (∃ fuel, program.runMain fuel 0 (words input) initial = .returned values final) ↔
      ∃ result : Env Bank, (∃ fuel, (source nonzero pred add).run evalOp fuel input = some result) ∧
        values = words result ∧ final = initial := by
  constructor
  · rintro ⟨fuel, ran⟩
    have enough := main_mono fuel (4 * fuel + 2) (by omega) input initial final values ran
    have agrees := main_aligned nonzero pred add evalOp nz dec sum fuel input initial
    rw [enough, returned] at agrees
    obtain ⟨result, h, eq⟩ := Option.map_eq_some_iff.mp agrees.symm
    exact ⟨result, ⟨fuel, h⟩, (Prod.mk.inj eq).1.symm, (Prod.mk.inj eq).2.symm⟩
  · rintro ⟨result, ⟨fuel, ran⟩, rfl, rfl⟩
    refine ⟨4 * fuel + 2, returned_eq.mp ?_⟩
    rw [main_aligned nonzero pred add evalOp nz dec sum, ran]
    rfl

theorem fromWords_words : ∀ input : Env Bank, fromWords (words input) = some input
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem words_injective : Function.Injective words := by
  intro a b same
  simpa only [fromWords_words, Option.some.injEq] using congrArg fromWords same

theorem returns_iff_scf {Op : OpSignature} {loop : While Op Bank Bank}
    (image : Image loop) (evalOp : Eval Op) (agreement : image.Agrees evalOp)
    (input : Env Bank) (initial final : Memory) (values : List Word) :
    (∃ fuel, (lower image).runMain fuel 0 (words input) initial = .returned values final) ↔
      ∃ result : Env Bank, (∃ fuel, loop.run evalOp fuel input = some result) ∧
        values = words result ∧ final = initial := by
  change (∃ fuel, program.runMain fuel 0 (words input) initial = .returned values final) ↔ _
  rw [image.shape]
  exact returns_iff image.nonzero image.pred image.add evalOp
    agreement.nonzero agreement.pred agreement.add input initial final values

section Peggy

open Silmaril.SSA.PEG
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open Silmaril.SSA.RVSDG (Port Tuple)

open Silmaril.SSA.PEG.Bridge.Theta.Region

variable {Data : Type} {P : InstructionSet.{0,0} Data} {left right : Data} {n : Nat}
variable {g : Graph P (pegSlots left right) (pegSlots left right) n 1} {t : Silmaril.SSA.PEG.Ty Data}
variable {slot : Port (pegSlots left right) t} {invariants : Bool}
variable (b : Bundle g slot invariants)
variable (evalOp : Eval (MLIR.Opcode (wordProfile Data) P))
variable (image : Image (MLIR.lower (wordProfile Data) b))
variable (agreement : image.Agrees evalOp)
variable (neg : ∀ flag : Bool,
  (MLIR.model (wordProfile Data) evalOp).run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)


include agreement neg in
theorem returns_iff_observe (input : Env Bank) (initial final : Memory) (values : List Word) (idx : Index 1) :
    let m := MLIR.model (wordProfile Data) evalOp
    let decode := (wordProfile Data).decode (pegSlots left right)
    (∃ fuel, (lower image).runMain fuel 0 (words input) initial = .returned values final) ↔
      ∃ result : Env Bank,
        g.observe m.toPEG (g.denote m.toPEG (decode input) b.demandWellFounded) idx =
          (decode result).map (fun _ => some) ∧ values = words result ∧ final = initial := by
  dsimp only
  rw [returns_iff_scf image evalOp agreement]
  exact exists_congr fun result =>
    and_congr (MLIR.returns_iff_observe (wordProfile Data) evalOp b neg input result idx) Iff.rfl

include agreement neg in
theorem returns_iff_observe_bank (input result : Env Bank) (initial final : Memory) (idx : Index 1) :
    let m := MLIR.model (wordProfile Data) evalOp
    let decode := (wordProfile Data).decode (pegSlots left right)
    (∃ fuel, (lower image).runMain fuel 0 (words input) initial = .returned (words result) final) ↔
      g.observe m.toPEG (g.denote m.toPEG (decode input) b.demandWellFounded) idx =
        (decode result).map (fun _ => some) ∧ final = initial := by
  have simulated :=
    returns_iff_observe b evalOp image agreement neg input initial final (words result) idx
  constructor
  · intro ran
    obtain ⟨other, observed, same, unchanged⟩ := simulated.mp ran
    obtain rfl := words_injective same
    exact ⟨observed, unchanged⟩
  · rintro ⟨observed, unchanged⟩
    exact simulated.mpr ⟨result, observed, rfl, unchanged⟩

include agreement neg in
theorem firstExit_of_run (input : Env Bank) (initial final : Memory) (values : List Word) (idx : Index 1)
    (fuel : Nat) (ran : (lower image).runMain fuel 0 (words input) initial = .returned values final) :
    let m := MLIR.model (wordProfile Data) evalOp
    let decode := (wordProfile Data).decode (pegSlots left right)
    ∃ (result : Env Bank) (k : Nat) (finalBank : Tuple m.toPEG.Value (.bool :: pegSlots left right)),
      values = words result ∧ final = initial ∧ carriedValues finalBank = decode result ∧
        b.scalar.TraceObservation m.toPEG
          (g.denote m.toPEG (decode input) b.demandWellFounded) idx k finalBank := by
  obtain ⟨result, ⟨scfFuel, scfRan⟩, rfl, rfl⟩ :=
    (returns_iff_scf image evalOp agreement input initial final values).mp ⟨fuel, ran⟩
  obtain ⟨k, finalBank, bankEq, trace⟩ :=
    MLIR.firstExit_of_run (wordProfile Data) evalOp b neg input result idx scfFuel scfRan
  exact ⟨result, k, finalBank, rfl, rfl, bankEq, trace⟩

end Peggy

end Silmaril.Machine.PEG.CountedLoop.Proofs
