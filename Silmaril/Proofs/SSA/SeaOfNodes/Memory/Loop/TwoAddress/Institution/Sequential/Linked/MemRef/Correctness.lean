module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame Edge Terminator)
open Silmaril.MLIR.CF.Ordered (Block runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.MemRef.CF (wordWidth resultTypes)
open TwoAddress.MemRef (Runtime)

variable {cells : Nat} {ambient next args : List ValueSort} {scope delta : List Width}

set_option backward.isDefEq.respectTransparency false

private abbrev SourceBlock (cells : Nat) (args : List ValueSort) (scope : List Width) :=
  Block (TwoAddress.MemRef.Body cells args) (TwoAddress.MemRef.Label cells) scope resultTypes

private abbrev LinkedBlock (cells : Nat) (ambient next : List ValueSort) (scope : List Width) :=
  Block (Body cells ambient next) (Label cells) scope pairTypes

private def sourceRun (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (block : SourceBlock cells args scope) (env : Env scope) (initial : Buffer cells) :
    Option (Option (Env resultTypes) × Buffer cells) :=
  (runBlock (TwoAddress.MemRef.lower cells graph).block (Block.eval (TwoAddress.MemRef.evalBody input))
    .nil fuel block env).run initial

private def linkedRun (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (block : LinkedBlock cells ambient next scope) (env : Env scope) (initial : Buffer cells) :
    Option (Option (Env pairTypes) × Buffer cells) :=
  (runBlock (lower cells first second).block (Block.eval (evalBody wiring input)) .nil fuel block env).run initial

private theorem run_succ {BlockTy : List Width → Type} {L : List Width → Type} {result : List Width}
    (nextBlock : ∀ {ins}, L ins → BlockTy (ins ++ []))
    (eval : ∀ {ins}, BlockTy ins → Env ins → Runtime cells (Frame L ⊕ Env result))
    (fuel : Nat) (block : BlockTy scope) (env : Env scope) (initial : Buffer cells) :
    (runBlock nextBlock eval .nil (fuel + 1) block env).run initial =
      ((eval block env).run initial).bind (fun (out, buffer) =>
        match out with
        | .inl frame => (runBlock nextBlock eval .nil fuel (nextBlock frame.label) (frame.args.append .nil)).run buffer
        | .inr values => some (some values, buffer)) := by
  conv_lhs => unfold runBlock
  simp only [StateT.run, Bind.bind, StateT.bind, Pure.pure]
  cases eval block env initial with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨out, buffer⟩
    cases out <;> rfl

private theorem carryOperands_eval (word : Word) (env : Env scope) (operands : Operands scope delta) :
    (carryOperands operands).eval (Env.cons (w := wordWidth) word env) = operands.eval env := by
  induction operands with
  | nil => rfl
  | cons _ _ ih =>
    simp only [carryOperands, Operands.eval, ih]
    rfl

private def firstTarget (out : Frame (TwoAddress.MemRef.Label cells) ⊕ Env resultTypes) :
    Frame (Label cells) ⊕ Env pairTypes :=
  .inl (match out with
    | .inl frame => ⟨.first frame.label, frame.args⟩
    | .inr values => ⟨.secondEntry, values⟩)

private def secondTarget (word : Word) (out : Frame (TwoAddress.MemRef.Label cells) ⊕ Env resultTypes) :
    Frame (Label cells) ⊕ Env pairTypes :=
  match out with
  | .inl frame => .inl ⟨.second frame.label, .cons word frame.args⟩
  | .inr values => .inr (.cons word values)

private theorem firstTerm_eval (term : Terminator (TwoAddress.MemRef.Label cells) resultTypes scope)
    (env : Env scope) : (firstTerm term).eval env = firstTarget (term.eval env) := by
  cases term with
  | br edge => rfl
  | condBr test yes no =>
    simp only [firstTerm, Terminator.eval]
    split <;> rfl
  | ret values => rfl

private theorem secondTerm_eval (word : Word) (term : Terminator (TwoAddress.MemRef.Label cells) resultTypes scope)
    (env : Env scope) : (secondTerm term).eval (.cons word env) = secondTarget word (term.eval env) := by
  cases term with
  | br edge => simp only [secondTerm, Terminator.eval, secondEdge, Edge.eval, Operands.eval, Env.get,
      carryOperands_eval, secondTarget]
  | condBr test yes no =>
    simp only [secondTerm, Terminator.eval]
    rw [show (Env.cons (w := wordWidth) word env).get (.there test) = env.get test from rfl]
    split <;> simp only [secondEdge, Edge.eval, Operands.eval, Env.get, carryOperands_eval, secondTarget]
  | ret values => simp only [secondTerm, Terminator.eval, Operands.eval, Env.get, carryOperands_eval, secondTarget]

private theorem firstBlock_eval (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (block : SourceBlock cells ambient scope) (env : Env scope) (initial : Buffer cells) :
    (Block.eval (evalBody wiring input) (firstBlock block) env).run initial =
      ((Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial).map
        (fun (out, buffer) => (firstTarget out, buffer)) := by
  change (((TwoAddress.MemRef.evalBody input block.body env).run initial).bind fun (values, buffer) =>
    some ((firstTerm block.terminator).eval values, buffer)) =
    (((TwoAddress.MemRef.evalBody input block.body env).run initial).bind fun (values, buffer) =>
      some (block.terminator.eval values, buffer)).map _
  cases (TwoAddress.MemRef.evalBody input block.body env).run initial with
  | none => rfl
  | some run => rcases run with ⟨values, buffer⟩; simp only [Option.bind_some, Option.map_some, firstTerm_eval]

private theorem secondBlock_eval (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (word : Word) (block : SourceBlock cells next scope) (env : Env scope) (initial : Buffer cells) :
    (Block.eval (evalBody wiring input) (secondBlock block) (.cons word env)).run initial =
      ((Block.eval (TwoAddress.MemRef.evalBody (wiring.select word input)) block env).run initial).map
        (fun (out, buffer) => (secondTarget word out, buffer)) := by
  let step := (TwoAddress.MemRef.evalBody (wiring.select word input) block.body env).run initial
  change ((step.bind fun (values, buffer) => some (Env.cons (w := wordWidth) word values, buffer)).bind
    fun (values, buffer) => some ((secondTerm block.terminator).eval values, buffer)) =
      (step.bind fun (values, buffer) => some (block.terminator.eval values, buffer)).map _
  cases step with
  | none => rfl
  | some run => rcases run with ⟨values, buffer⟩; simp only [Option.bind_some, Option.map_some, secondTerm_eval]

private theorem second_run (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (word : Word) (fuel : Nat) (block : SourceBlock cells next scope) (env : Env scope) (initial : Buffer cells) :
    linkedRun first second wiring input fuel (secondBlock block) (.cons word env) initial =
      (sourceRun second (wiring.select word input) fuel block env initial).map
        (fun (returned, final) => (returned.map (Env.cons (w := wordWidth) word), final)) := by
  induction fuel generalizing scope initial with
  | zero => rfl
  | succ fuel ih =>
    rw [linkedRun, sourceRun, run_succ, run_succ, secondBlock_eval]
    cases (Block.eval (TwoAddress.MemRef.evalBody (wiring.select word input)) block env).run initial with
    | none => rfl
    | some evaluated =>
      rcases evaluated with ⟨out, buffer⟩
      cases out with
      | inl frame =>
        exact ih ((TwoAddress.MemRef.lower cells second).block frame.label) (frame.args.append .nil) buffer
      | inr values => rfl

private def wordEnv (word : Word) : Env resultTypes := .cons word .nil
private def pairEnv (word nextWord : Word) : Env pairTypes := .cons word (wordEnv nextWord)

private theorem source_succ (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (block : SourceBlock cells args scope) (env : Env scope) (initial : Buffer cells) :
    sourceRun graph input (fuel + 1) block env initial =
      ((Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial).bind
        (fun (out, buffer) => match out with
          | .inl frame => sourceRun graph input fuel ((TwoAddress.MemRef.lower cells graph).block frame.label)
              (frame.args.append .nil) buffer
          | .inr values => some (some values, buffer)) := by
  unfold sourceRun
  rw [run_succ]
  cases (Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨out, buffer⟩
    cases out <;> rfl

private theorem linked_first_succ (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (block : SourceBlock cells ambient scope) (env : Env scope) (initial : Buffer cells) :
    linkedRun first second wiring input (fuel + 1) (firstBlock block) env initial =
      ((Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial).bind
        (fun (out, buffer) => match out with
          | .inl frame => linkedRun first second wiring input fuel
              (firstBlock ((TwoAddress.MemRef.lower cells first).block frame.label)) (frame.args.append .nil) buffer
          | .inr values => linkedRun first second wiring input fuel
              ((lower cells first second).block .secondEntry) (values.append .nil) buffer) := by
  rw [linkedRun, run_succ, firstBlock_eval]
  cases (Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨out, buffer⟩
    cases out <;> rfl

private theorem second_entry_success (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (reserved word nextWord : Word) (fuel : Nat) (middle final : Buffer cells) :
    linkedRun first second wiring input fuel ((lower cells first second).block .secondEntry)
        (wordEnv reserved) middle = some (some (pairEnv word nextWord), final) ↔
      reserved = word ∧
        sourceRun second (wiring.select reserved input) fuel (TwoAddress.MemRef.lower cells second).entry
          .nil middle = some (some (wordEnv nextWord), final) := by
  change linkedRun first second wiring input fuel (secondBlock (TwoAddress.MemRef.lower cells second).entry)
    (.cons reserved .nil) middle = _ ↔ _
  rw [second_run]
  constructor
  · intro success
    obtain ⟨⟨returned, buffer⟩, source, equal⟩ := Option.map_eq_some_iff.mp success
    cases returned with
    | none => cases equal
    | some values =>
      cases values with
      | cons result tail =>
        cases tail
        cases equal
        exact ⟨rfl, source⟩
  · rintro ⟨rfl, source⟩
    rw [source]
    rfl

private theorem split_first (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (block : SourceBlock cells ambient scope) (env : Env scope)
    (initial : Buffer cells) (word nextWord : Word) (final : Buffer cells)
    (success : linkedRun first second wiring input fuel (firstBlock block) env initial =
      some (some (pairEnv word nextWord), final)) :
    ∃ firstFuel secondFuel middle,
      sourceRun first input firstFuel block env initial = some (some (wordEnv word), middle) ∧
      sourceRun second (wiring.select word input) secondFuel (TwoAddress.MemRef.lower cells second).entry
        .nil middle = some (some (wordEnv nextWord), final) := by
  induction fuel generalizing scope initial with
  | zero => cases success
  | succ fuel ih =>
    rw [linked_first_succ] at success
    cases step : (Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial with
    | none =>
      rw [step] at success
      cases success
    | some evaluated =>
      rw [step] at success
      rcases evaluated with ⟨out, buffer⟩
      cases out with
      | inl frame =>
        have continued : linkedRun first second wiring input fuel
            (firstBlock ((TwoAddress.MemRef.lower cells first).block frame.label)) (frame.args.append .nil) buffer =
            some (some (pairEnv word nextWord), final) := success
        obtain ⟨f₁, f₂, middle, left, right⟩ := ih _ _ _ continued
        refine ⟨f₁ + 1, f₂, middle, ?_, right⟩
        rw [source_succ, step]
        exact left
      | inr values =>
        cases values with
        | cons reserved tail =>
          cases tail
          obtain ⟨rfl, right⟩ := (second_entry_success first second wiring input reserved word nextWord fuel buffer final).mp
            success
          refine ⟨1, fuel, buffer, ?_, right⟩
          rw [source_succ, step]
          rfl

private theorem join_first (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (firstFuel secondFuel : Nat) (block : SourceBlock cells ambient scope) (env : Env scope)
    (initial : Buffer cells) (word nextWord : Word) (middle final : Buffer cells)
    (left : sourceRun first input firstFuel block env initial = some (some (wordEnv word), middle))
    (right : sourceRun second (wiring.select word input) secondFuel (TwoAddress.MemRef.lower cells second).entry
      .nil middle = some (some (wordEnv nextWord), final)) :
    ∃ fuel, linkedRun first second wiring input fuel (firstBlock block) env initial =
      some (some (pairEnv word nextWord), final) := by
  induction firstFuel generalizing scope initial with
  | zero => cases left
  | succ firstFuel ih =>
    rw [source_succ] at left
    cases step : (Block.eval (TwoAddress.MemRef.evalBody input) block env).run initial with
    | none =>
      rw [step] at left
      cases left
    | some evaluated =>
      rw [step] at left
      rcases evaluated with ⟨out, buffer⟩
      cases out with
      | inl frame =>
        obtain ⟨fuel, returned⟩ := ih ((TwoAddress.MemRef.lower cells first).block frame.label) (frame.args.append .nil)
          buffer left
        refine ⟨fuel + 1, ?_⟩
        rw [linked_first_succ, step]
        exact returned
      | inr values =>
        change some (some values, buffer) = some (some (wordEnv word), middle) at left
        cases left
        refine ⟨secondFuel + 1, ?_⟩
        rw [linked_first_succ, step]
        exact (second_entry_success first second wiring input word word nextWord secondFuel middle final).mpr ⟨rfl, right⟩

private theorem source_success (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) (word : Word) (final : Buffer cells) :
    TwoAddress.MemRef.runFuel graph input fuel initial = some (word, final) ↔
      sourceRun graph input fuel (TwoAddress.MemRef.lower cells graph).entry .nil initial =
        some (some (wordEnv word), final) := by
  change ((sourceRun graph input fuel (TwoAddress.MemRef.lower cells graph).entry .nil initial).bind
    fun (returned, heap) => returned.map (fun values => (values.get .here, heap))) = _ ↔ _
  cases sourceRun graph input fuel (TwoAddress.MemRef.lower cells graph).entry .nil initial with
  | none => simp
  | some pair =>
    rcases pair with ⟨returned, heap⟩
    cases returned with
    | none => simp
    | some values =>
      cases values with
      | cons value tail => cases tail; simp [wordEnv, Env.get]

private theorem linked_success (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (initial : Buffer cells) (word nextWord : Word) (final : Buffer cells) :
    runFuel first second wiring input fuel initial = some (word, nextWord, final) ↔
      linkedRun first second wiring input fuel (firstBlock (TwoAddress.MemRef.lower cells first).entry) .nil initial =
        some (some (pairEnv word nextWord), final) := by
  change ((linkedRun first second wiring input fuel (firstBlock (TwoAddress.MemRef.lower cells first).entry)
      .nil initial).bind fun (returned, heap) =>
    returned.map (fun values => (values.get .here, values.get (.there .here), heap))) = _ ↔ _
  cases linkedRun first second wiring input fuel (firstBlock (TwoAddress.MemRef.lower cells first).entry)
      .nil initial with
  | none => simp
  | some pair =>
    rcases pair with ⟨returned, heap⟩
    cases returned with
    | none => simp
    | some values =>
      cases values with
      | cons firstValue values =>
        cases values with
        | cons secondValue tail =>
          cases tail
          simp [pairEnv, wordEnv, Env.get, and_assoc]

theorem returns_iff_stages (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (initial : Buffer cells) (word nextWord : Word) (final : Buffer cells) :
    (∃ fuel, runFuel first second wiring input fuel initial = some (word, nextWord, final)) ↔
      ∃ firstFuel secondFuel middle,
        TwoAddress.MemRef.runFuel first input firstFuel initial = some (word, middle) ∧
        TwoAddress.MemRef.runFuel second (wiring.select word input) secondFuel middle = some (nextWord, final) := by
  simp only [linked_success, source_success]
  constructor
  · rintro ⟨fuel, returned⟩
    exact split_first first second wiring input fuel _ _ initial word nextWord final returned
  · rintro ⟨f₁, f₂, middle, left, right⟩
    exact join_first first second wiring input f₁ f₂ _ _ initial word nextWord middle final left right

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Proofs
