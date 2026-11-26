module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Proofs

open Silmaril.Isotope (Value)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame CallOracle Opcode packValues)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith emitOpsWithResults)
open Silmaril.SSA.RVSDG (Port)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}

private def NoCalls (op : Op Reg) : Prop :=
  match op with
  | .call .. => False
  | _ => True

private theorem callsMatch_of_noCalls {fn : Func Reg} (signature : List Silmaril.Machine.RTL.Signature)
    (pureOps : ∀ b ∈ fn.blocks, ∀ op ∈ b.ops, NoCalls op) : fn.CallsMatch signature := by
  rw [Func.CallsMatch, Func.callsMatch, List.all_eq_true]
  intro b member
  rw [List.all_eq_true]
  intro op used
  have quiet := pureOps b member op used
  cases op <;> simp_all [NoCalls]

private theorem pure_preheader {args : List PortTy} {past table : List (List PortTy)}
    (flow : Dataflow WordOp args past table)
    (arg : ∀ {t}, Port args t → Reg) (result : Nat → Reg) :
    ∀ op ∈ emitOpsWithResults (fun p => arg p) result flow, NoCalls op := by
  induction flow with
  | nil => simp [emitOpsWithResults]
  | cons instr wires rest ih =>
    intro op member
    rcases List.mem_cons.mp member with rfl | there
    · cases instr <;> trivial
    · exact ih op there

private theorem pure_header {args : List PortTy} {past table : List (List PortTy)}
    (flow : Dataflow WordOp args past table) (arg : ∀ {t}, Port args t → Reg) :
    ∀ op ∈ emitOpsWith (fun p => arg p) flow, NoCalls op := by
  induction flow with
  | nil => simp [emitOpsWith]
  | cons instr wires rest ih =>
    intro op member
    rcases List.mem_cons.mp member with rfl | there
    · cases instr <;> trivial
    · exact ih op there

private theorem empty_dispatch {captures bank n : Nat}
    (rows : Choices captures bank sigs n) (first : Nat) :
    ∀ b ∈ rows.blocks first, b.ops = [] := by
  induction rows generalizing first with
  | last column => simp [Choices.blocks]
  | test selector column tail ih =>
    intro b member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · exact ih (first + 1) b later

theorem callsMatch (p : Source new old entrySigs sigs tests) :
    (lowerFunc p).CallsMatch [⟨new, 1⟩] := by
  apply callsMatch_of_noCalls
  intro b member op used
  rcases List.mem_append.mp member with first | chain
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at first
    rcases first with rfl | rfl | rfl
    · exact pure_preheader p.primary.preheader _ _ op used
    · exact pure_header p.primary.header _ op used
    · cases used
  · rw [empty_dispatch p.rows 3 b chain] at used
    cases used

private def ofWords : (args : List Word) → WordTuple args.length
  | [] => .nil
  | w :: ws => .cons w (ofWords ws)

private theorem words_ofWords (args : List Word) : words (ofWords args) = args := by
  induction args with
  | nil => rfl
  | cons w ws ih => exact congrArg (w :: ·) ih

private theorem typed_input (args : List Word) (width : args.length = new) :
    ∃ input : WordTuple new, words input = args := by
  subst new
  exact ⟨ofWords args, words_ofWords args⟩

private theorem oracle_matches (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog) :
    CallOracle.MatchesSigs prog.oracle [⟨new, 1⟩] := by
  have actual := (lowerChecked_sound mapping p accepted).2.1
  intro f args initial returned final run
  have witness := run
  obtain ⟨s, start, _⟩ := witness
  obtain ⟨point, fr, enter, _⟩ := Prog.start_eq_some_iff.mp start
  rw [actual] at enter
  cases f with
  | zero =>
    change ((Frame.empty.writeAll (paramRegs 0 new) args).map (fun fr => (⟨0, 0, 0⟩, fr))) =
      some (point, fr) at enter
    obtain ⟨ready, wrote, _⟩ := Option.map_eq_some_iff.mp enter
    have len := writeAll_length wrote
    have arity : args.length = new := by simpa [paramRegs] using len.symm
    obtain ⟨input, rfl⟩ := (typed_input args arity).imp (fun input eq => eq.symm)
    obtain ⟨_, value, _, rfl, _⟩ := (rtl_return_iff mapping p accepted input initial final returned).mp run
    rfl
  | succ f =>
    simp [Prog.enter, Prog.func?, lowerRTL] at enter

theorem region_exit_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (env : Env Word) (entry : env 0 = packValues (words input))
    (initial final : Memory) (value : Value Word) :
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) prog.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping p))) initial 0 value final ↔
      ∃ returned, value = packValues returned ∧ prog.oracle 0 (words input) initial returned final := by
  let fn := lowerFunc (mapCaptures mapping p)
  have actual := (lowerChecked_sound mapping p accepted).2.1
  have funcFound : prog.func? 0 = some fn := by rw [actual]; rfl
  have blockFound : fn.block? fn.entry = some (Width.preheader (mapCaptures mapping p).primary) := rfl
  have wrote : Frame.empty.writeAll (Width.preheader (mapCaptures mapping p).primary).params (words input) =
      some (bindWords 0 Frame.empty input) := bindWords_write 0 Frame.empty input
  rw [toLambdaSSA_eval_iff (lowerFunc_wellFormed _) (oracle_matches mapping p accepted)
    (callsMatch _) blockFound wrote entry]
  simp only [Nat.zero_ne_one, false_and, or_false, true_and]
  constructor
  · rintro ⟨ret, rfl, run⟩
    exact ⟨ret, rfl, (Func.exec_returned_iff_oracle funcFound blockFound wrote).mp run⟩
  · rintro ⟨ret, rfl, run⟩
    exact ⟨ret, rfl, (Func.exec_returned_iff_oracle funcFound blockFound wrote).mpr run⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Proofs
