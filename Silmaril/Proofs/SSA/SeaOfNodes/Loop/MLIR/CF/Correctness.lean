module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.MLIR.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Proofs

open Diamond (Val ValueSort dataPorts)
open RVSDG (Tuple Wires Locals extend)
open SeaOfNodes.MLIR (Word sourceInputs)
open SeaOfNodes.MLIR.Lowering
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

theorem opcode_correct {ins : List (ValueSort Width)} {out : ValueSort Width}
    (op : Op ins out) (input : Tuple (Val Word) (dataPorts ins)) :
    evalOp (opcode op) (encodeValues input) = valueBits (model.run op input) := by
  cases op with
  | arithmetic op =>
    cases op with
    | constant => cases input; rfl
    | binary =>
      cases input with | cons x tail =>
      cases tail with | cons y tail =>
      cases tail
      rfl
  | ult | slt =>
    cases input with | cons x tail =>
    cases tail with | cons y tail =>
    cases tail
    rfl

private theorem append_names {Δ : List Width} {left right : List (Diamond.Ty Width)}
    {env : Env Δ} {names : Tuple (Names Δ) left} {values : Tuple (Val Word) left}
    {suffix : Tuple (Names Δ) right} {tail : Tuple (Val Word) right}
    (first : NamesAgree env names values) (last : NamesAgree env suffix tail) :
    NamesAgree env (appendTuple suffix names) (appendTuple tail values) := by
  induction names with
  | nil => cases values; exact last
  | cons name names ih =>
    cases values with
    | cons value values =>
      intro s port
      cases port with
      | head => exact first .head
      | tail port => exact ih (fun pos => first (.tail pos)) port

open Bank (Values bankEnv bankOperands prependNames bankNames)

private theorem captured_names (input : Env Γ) {widths : List Width} (old : Values widths) :
    NamesAgree ((bankEnv old).append input) (prependNames widths (inputNames Γ)) (sourceInputs input) := by
  induction widths with
  | nil => exact inputs_agree input
  | cons width rest ih =>
    cases old with
    | cons value tail => exact weaken_names (ih tail) value

private theorem carried_names (input : Env Γ) {widths : List Width} (old : Values widths) :
    NamesAgree ((bankEnv old).append input) (bankNames Γ widths) old := by
  induction widths with
  | nil => intro sort port; cases port
  | cons width rest ih =>
    cases old with
    | cons value tail =>
      intro sort port
      cases port with
      | head => rfl
      | tail p => exact weaken_names (ih tail) value p

theorem headerScope_agrees (input : Env Γ) (old : Values carried) :
    (Bank.headerScope Γ carried).Agrees ((bankEnv old).append input)
      (appendTuple old (sourceInputs input)) PUnit.unit :=
  ⟨append_names (captured_names input old) (carried_names input old), trivial⟩

private theorem bankOperands_eval {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    {Δ widths : List Width} {scope : Scope args past Δ} {env : Env Δ}
    {values : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env values locals) (wires : Wires args past (dataPorts (inputSorts widths))) :
    (bankOperands scope wires).eval env = bankEnv (wires.read values locals) := by
  induction widths with
  | nil => rfl
  | cons width rest ih =>
    cases wires with
    | cons wire tail =>
      change Env.cons (env.get (scope.resolveValue wire)) ((bankOperands scope tail).eval env) =
        Env.cons (Diamond.read model wire values locals) (bankEnv (Wires.read tail values locals))
      rw [ok.resolve wire, ih tail]
      rfl

private def headerFrame (values : Values carried) : Frame (Bank.Label carried result) :=
  ⟨.header, bankEnv values⟩

private def exitFrame (value : Word result) : Frame (Bank.Label carried result) :=
  ⟨.exit, .cons value .nil⟩

private def resultEnv (value : Word result) : Env [result] :=
  .cons value .nil

private def stepFrame : Word result ⊕ Values carried → Frame (Bank.Label carried result)
  | .inl value => exitFrame value
  | .inr next => headerFrame next

variable (g : Bank.Program Γ carried result entrySigs headerSigs) (input : Env Γ)

private theorem entry_eval :
    (Bank.lower g).entry.eval evalOp (fun term env => term.eval env) input =
      .inl (headerFrame (g.initial model (sourceInputs input))) := by
  refine lowerCode_eval opcode evalOp model.run opcode_correct g.preheader _ input (sourceInputs input) PUnit.unit
    ⟨inputs_agree input, trivial⟩ (Bank.entryTerm g) (fun term env => term.eval env) _ ?_
  intro Δ scope env ok
  exact congrArg (fun args => Sum.inl (Frame.mk Bank.Label.header args))
    (bankOperands_eval ok (g.phiInputs .entry))

private theorem header_eval (old : Values carried) :
    ((Bank.lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl (stepFrame (g.step model (sourceInputs input) old)) := by
  let args := appendTuple old (sourceInputs input)
  have bindings : (Bank.headerScope Γ carried).Agrees ((bankEnv old).append input) args PUnit.unit :=
    headerScope_agrees input old
  refine lowerCode_eval opcode evalOp model.run opcode_correct g.header _ _ args _ bindings
    (Bank.headerTerm g) (fun term env => term.eval env) _ ?_
  intro Δ scope env ok
  let locals := g.header.eval model args PUnit.unit
  have testBit (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by cases b <;> rfl
  have guard : (env.get (scope.resolveValue g.predicate)).getLsbD 0 =
      (Diamond.read model g.predicate args locals).down :=
    (congrArg (fun bits : BitVec 1 => bits.getLsbD 0) (ok.resolve g.predicate)).trans
      (testBit (Diamond.read model g.predicate args locals).down)
  have update : (bankOperands scope (g.phiInputs .backedge)).eval env =
      bankEnv (g.latch model .backedge args locals) :=
    bankOperands_eval ok (g.phiInputs .backedge)
  have readback : env.get (scope.resolveValue g.result) = Diamond.read model g.result args locals :=
    ok.resolve g.result
  change Sum.inl (if (env.get (scope.resolveValue g.predicate)).getLsbD 0 then
      (⟨.header, (bankOperands scope (g.phiInputs .backedge)).eval env⟩ : Frame (Bank.Label carried result))
    else exitFrame (env.get (scope.resolveValue g.result))) = _
  erw [guard, update, readback]
  have route (test : Bool) (next : Values carried) (out : Word result) :
      (if test then headerFrame next else exitFrame out) =
        stepFrame (if test then .inr next else .inl out) := by
    cases test <;> rfl
  exact congrArg Sum.inl (route _ _ _)

private theorem run_entry (fuel : Nat) :
    (Bank.lower g).run evalOp (fuel + 1) input =
      (Bank.lower g).runFrom evalOp fuel input (headerFrame (g.initial model (sourceInputs input))) := by
  unfold Cfg.run
  rw [Cfg.runBlock, entry_eval]
  rfl

theorem entry_frame :
    (Bank.lower g).entry.eval evalOp (fun term env => term.eval env) input =
      .inl ⟨.header, bankEnv (g.initial model (sourceInputs input))⟩ :=
  entry_eval g input

theorem header_frame (old : Values carried) :
    ((Bank.lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl (match g.step model (sourceInputs input) old with
        | .inl value => ⟨.exit, .cons value .nil⟩
        | .inr next => ⟨.header, bankEnv next⟩) :=
  header_eval g input old

private theorem run_header (fuel : Nat) (old : Values carried) :
    (Bank.lower g).runFrom evalOp (fuel + 1) input (headerFrame old) =
      (Bank.lower g).runFrom evalOp fuel input (stepFrame (g.step model (sourceInputs input) old)) := by
  change (Bank.lower g).runBlock evalOp input (fuel + 1) ((Bank.lower g).block .header) ((bankEnv old).append input) = _
  rw [Cfg.runBlock, header_eval]
  rfl

private theorem run_header_budget (budget : Nat) (old : Values carried) :
    (Bank.lower g).runFrom evalOp (budget + 2) input (headerFrame old) =
      (g.evalFrom model (sourceInputs input) budget old).map resultEnv := by
  induction budget generalizing old with
  | zero =>
    erw [Graph.evalFrom.eq_1 g model (sourceInputs input) old]
    rw [show 0 + 2 = 1 + 1 by rfl, run_header]
    cases g.step model (sourceInputs input) old with
    | inl value => rfl
    | inr next => exact run_header g input 0 next
  | succ fuel ih =>
    erw [Graph.evalFrom.eq_2 g model (sourceInputs input) old fuel]
    rw [show fuel + 1 + 2 = (fuel + 2) + 1 by rfl, run_header]
    cases g.step model (sourceInputs input) old with
    | inl value => rfl
    | inr next => exact ih next

theorem run_budget (budget : Nat) :
    (Bank.lower g).run evalOp (budget + 3) input =
      (g.evalBackedges model budget (sourceInputs input)).map (fun value => Env.cons value .nil) := by
  erw [show budget + 3 = (budget + 2) + 1 by rfl, run_entry, run_header_budget]
  rfl

theorem returns_iff (value : Word result) :
    g.Returns model (sourceInputs input) value ↔
      ∃ fuel, (Bank.lower g).run evalOp fuel input = some (.cons value .nil) := by
  refine (g.returns_iff_evalBackedges model (sourceInputs input) value).trans ?_
  constructor
  · rintro ⟨budget, run⟩
    exact ⟨budget + 3, by rw [run_budget, run]; rfl⟩
  · rintro ⟨fuel, run⟩
    rcases fuel with _ | fuel
    · cases run
    rcases fuel with _ | fuel
    · rw [run_entry] at run
      cases run
    rcases fuel with _ | budget
    · erw [run_entry, run_header] at run
      cases run
    erw [run_budget, Option.map_eq_some_iff] at run
    obtain ⟨other, observed, same⟩ := run
    exact ⟨budget, observed.trans (congrArg (fun env : Env [result] => some (env.get .here)) same)⟩

theorem denotePart_eq :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (Bank.lower g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) := by
  apply Part.ext
  intro outcome
  rw [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff]
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, Option.map_eq_some_iff]
  constructor
  · rintro ⟨fuel, output, run, rfl⟩
    cases output with
    | cons value rest =>
      cases rest
      exact Part.mem_map _ ((g.returns_iff_mem_denote model (sourceInputs input) value).mp
        ((returns_iff g input value).mpr ⟨fuel, run⟩))
  · intro observed
    obtain ⟨value, returned, rfl⟩ := (Part.mem_map_iff _).mp observed
    obtain ⟨fuel, run⟩ := (returns_iff g input value).mp
      ((g.returns_iff_mem_denote model (sourceInputs input) value).mpr returned)
    exact ⟨fuel, _, run, rfl⟩

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Proofs
