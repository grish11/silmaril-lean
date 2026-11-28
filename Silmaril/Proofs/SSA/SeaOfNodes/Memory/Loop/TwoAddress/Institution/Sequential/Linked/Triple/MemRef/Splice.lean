module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame Edge Terminator)
open Silmaril.MLIR.CF.Ordered (Block Cfg runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.MemRef.CF (wordWidth resultTypes)
open Linked.MemRef (pairTypes carryOperands)
open TwoAddress.MemRef (Runtime)

variable {cells : Nat} {ambient next last : List ValueSort} {scope delta : List Width}

set_option backward.isDefEq.respectTransparency false

private def wordEnv (word : Word) : Env resultTypes := .cons word .nil
private def pairEnv (first second : Word) : Env pairTypes := .cons first (wordEnv second)

private theorem word_eta (words : Env resultTypes) : ∃ word, words = wordEnv word := by
  cases words with
  | cons word rest => cases rest; exact ⟨word, rfl⟩

private theorem pair_eta (words : Env pairTypes) : ∃ first second, words = pairEnv first second := by
  cases words with
  | cons first rest =>
    obtain ⟨second, rfl⟩ := word_eta rest
    exact ⟨first, second, rfl⟩

private theorem triple_eta (words : Env tripleTypes) :
    ∃ first second third, words = (pairEnv first second).append (wordEnv third) := by
  cases words with
  | cons first rest =>
    obtain ⟨second, third, rfl⟩ := pair_eta rest
    exact ⟨first, second, third, rfl⟩

private def pairTarget (out : Frame (Linked.MemRef.Label cells) ⊕ Env pairTypes) :
    Frame (Label cells) ⊕ Env tripleTypes :=
  .inl (match out with
    | .inl frame => ⟨.pair frame.label, frame.args⟩
    | .inr values => ⟨.thirdEntry, values⟩)

private def thirdTarget (words : Env pairTypes) (out : Frame (TwoAddress.MemRef.Label cells) ⊕ Env resultTypes) :
    Frame (Label cells) ⊕ Env tripleTypes :=
  match out with
  | .inl frame => .inl ⟨.third frame.label, words.append frame.args⟩
  | .inr values => .inr (words.append values)

private theorem pairTerm_eval (term : Terminator (Linked.MemRef.Label cells) pairTypes scope) (env : Env scope) :
    (pairTerm term).eval env = pairTarget (term.eval env) := by
  cases term with
  | br edge => rfl
  | condBr test yes no => simp only [pairTerm, Terminator.eval]; split <;> rfl
  | ret values => rfl

private theorem eval_keepPair (words : Env pairTypes) (env : Env scope) (args : Operands scope delta) :
    (keepPair args).eval (words.append env) = words.append (args.eval env) := by
  obtain ⟨first, second, rfl⟩ := pair_eta words
  change Env.cons (w := wordWidth) first (.cons (w := wordWidth) second
    ((carryOperands (carryOperands args)).eval (Env.cons (w := wordWidth) first (.cons (w := wordWidth) second env)))) =
      Env.cons (w := wordWidth) first (.cons (w := wordWidth) second (args.eval env))
  rw [Linked.MemRef.carryOperands_eval, Linked.MemRef.carryOperands_eval]

private theorem thirdTerm_eval (words : Env pairTypes)
    (term : Terminator (TwoAddress.MemRef.Label cells) resultTypes scope) (env : Env scope) :
    (thirdTerm term).eval (words.append env) = thirdTarget words (term.eval env) := by
  cases term with
  | br edge => simp only [thirdTerm, Terminator.eval, thirdEdge, Edge.eval, eval_keepPair, thirdTarget]
  | condBr test yes no =>
    obtain ⟨first, second, rfl⟩ := pair_eta words
    simp only [thirdTerm, Terminator.eval]
    rw [show ((pairEnv first second).append env).get (.there (.there test)) = env.get test from rfl]
    split <;> simp only [thirdEdge, Edge.eval, eval_keepPair, thirdTarget]
  | ret values => simp only [thirdTerm, Terminator.eval, eval_keepPair, thirdTarget]

private theorem pairBlock_eval (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient)
    (block : Block (Linked.MemRef.Body cells ambient next) (Linked.MemRef.Label cells) scope pairTypes)
    (env : Env scope) (initial : Buffer cells) :
    (Block.eval (evalBody f g input) (pairBlock block) env).run initial =
      ((Block.eval (Linked.MemRef.evalBody f input) block env).run initial).map
        (fun (out, buffer) => (pairTarget out, buffer)) := by
  let step := (Linked.MemRef.evalBody f input block.body env).run initial
  change (step.bind fun (values, buffer) => some ((pairTerm block.terminator).eval values, buffer)) =
    (step.bind fun (values, buffer) => some (block.terminator.eval values, buffer)).map _
  cases step with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨values, buffer⟩
    simp only [Option.bind_some, Option.map_some, pairTerm_eval]

private theorem thirdBlock_eval (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient) (words : Env pairTypes)
    (block : Block (TwoAddress.MemRef.Body cells last) (TwoAddress.MemRef.Label cells) scope resultTypes)
    (env : Env scope) (initial : Buffer cells) :
    (Block.eval (evalBody f g input) (thirdBlock block) (words.append env)).run initial =
      ((Block.eval (TwoAddress.MemRef.evalBody (selectThird f g input
          (words.get .here) (words.get (.there .here)))) block env).run initial).map
        (fun (out, buffer) => (thirdTarget words out, buffer)) := by
  obtain ⟨first, second, rfl⟩ := pair_eta words
  let step := (TwoAddress.MemRef.evalBody (selectThird f g input first second) block.body env).run initial
  change ((step.bind fun (values, buffer) => some ((Env.cons (w := wordWidth) first
      (.cons (w := wordWidth) second values)), buffer)).bind
    fun (values, buffer) => some ((thirdTerm block.terminator).eval values, buffer)) =
    (step.bind fun (values, buffer) => some (block.terminator.eval values, buffer)).map _
  cases step with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨values, buffer⟩
    exact congrArg (fun out => some (out, buffer)) (thirdTerm_eval (.cons first (.cons second .nil)) _ values)

private def runAt {Body : List Width → List Width → Type} {L : List Width → Type} {res : List Width}
    (cfg : Cfg Body L [] res) (eval : ∀ {ins outs}, Body ins outs → Env ins → Runtime cells (Env outs))
    (fuel : Nat) (block : Block Body L scope res) (env : Env scope) (initial : Buffer cells) :
    Option (Option (Env res) × Buffer cells) :=
  (runBlock cfg.block (Block.eval eval) .nil fuel block env).run initial

private theorem runAt_succ {Body : List Width → List Width → Type} {L : List Width → Type} {res : List Width}
    (cfg : Cfg Body L [] res) (eval : ∀ {ins outs}, Body ins outs → Env ins → Runtime cells (Env outs))
    (fuel : Nat) (block : Block Body L scope res) (env : Env scope) (initial : Buffer cells) :
    runAt cfg eval (fuel + 1) block env initial =
      ((Block.eval eval block env).run initial).bind (fun (out, buffer) =>
        match out with
        | .inl frame => runAt cfg eval fuel (cfg.block frame.label) (frame.args.append .nil) buffer
        | .inr values => some (some values, buffer)) := by
  unfold runAt
  conv_lhs => unfold runBlock
  simp only [StateT.run, Bind.bind, StateT.bind, Pure.pure]
  cases (Block.eval eval block env) initial with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨out, buffer⟩
    cases out <;> rfl

private abbrev PairBlock (cells : Nat) (ambient next : List ValueSort) (scope : List Width) :=
  Block (Linked.MemRef.Body cells ambient next) (Linked.MemRef.Label cells) scope pairTypes

private abbrev ThirdBlock (cells : Nat) (last : List ValueSort) (scope : List Width) :=
  Block (TwoAddress.MemRef.Body cells last) (TwoAddress.MemRef.Label cells) scope resultTypes

private theorem third_run (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (words : Env pairTypes) (fuel : Nat) (block : ThirdBlock cells last scope)
    (env : Env scope) (initial : Buffer cells) :
    runAt (lower cells first second third) (evalBody f g input) fuel (thirdBlock block) (words.append env) initial =
      (runAt (TwoAddress.MemRef.lower cells third)
        (TwoAddress.MemRef.evalBody (selectThird f g input (words.get .here) (words.get (.there .here))))
        fuel block env initial).map (fun (returned, final) => (returned.map words.append, final)) := by
  induction fuel generalizing scope initial with
  | zero => rfl
  | succ fuel ih =>
    rw [runAt_succ, runAt_succ, thirdBlock_eval]
    cases (Block.eval (TwoAddress.MemRef.evalBody
      (selectThird f g input (words.get .here) (words.get (.there .here)))) block env).run initial with
    | none => rfl
    | some evaluated =>
      rcases evaluated with ⟨out, buffer⟩
      cases out with
      | inl frame =>
        obtain ⟨firstWord, secondWord, rfl⟩ := pair_eta words
        exact ih ((TwoAddress.MemRef.lower cells third).block frame.label) (frame.args.append .nil) buffer
      | inr values => rfl

private theorem pair_run_succ (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (block : PairBlock cells ambient next scope) (env : Env scope) (initial : Buffer cells) :
    runAt (lower cells first second third) (evalBody f g input) (fuel + 1) (pairBlock block) env initial =
      ((Block.eval (Linked.MemRef.evalBody f input) block env).run initial).bind
        (fun (out, buffer) => match out with
          | .inl frame => runAt (lower cells first second third) (evalBody f g input) fuel
              (pairBlock ((Linked.MemRef.lower cells first second).block frame.label))
              (frame.args.append .nil) buffer
          | .inr values => runAt (lower cells first second third) (evalBody f g input) fuel
              ((lower cells first second third).block .thirdEntry) (values.append .nil) buffer) := by
  rw [runAt_succ, pairBlock_eval]
  cases (Block.eval (Linked.MemRef.evalBody f input) block env).run initial with
  | none => rfl
  | some evaluated =>
    rcases evaluated with ⟨out, buffer⟩
    cases out <;> rfl

private theorem entry_success (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (words : Env pairTypes) (fuel : Nat) (middle final : Buffer cells) (x y z : Word) :
    runAt (lower cells first second third) (evalBody f g input) fuel
        ((lower cells first second third).block .thirdEntry) (words.append .nil) middle =
          some (some ((pairEnv x y).append (wordEnv z)), final) ↔
      words = pairEnv x y ∧
        runAt (TwoAddress.MemRef.lower cells third)
          (TwoAddress.MemRef.evalBody (selectThird f g input x y)) fuel
          (TwoAddress.MemRef.lower cells third).entry .nil middle = some (some (wordEnv z), final) := by
  change runAt (lower cells first second third) (evalBody f g input) fuel
    (thirdBlock (TwoAddress.MemRef.lower cells third).entry) (words.append .nil) middle = _ ↔ _
  rw [third_run]
  constructor
  · intro success
    obtain ⟨⟨returned, buffer⟩, source, equal⟩ := Option.map_eq_some_iff.mp success
    cases returned with
    | none => cases equal
    | some values =>
      obtain ⟨firstWord, secondWord, rfl⟩ := pair_eta words
      obtain ⟨thirdWord, rfl⟩ := word_eta values
      cases equal
      exact ⟨rfl, source⟩
  · rintro ⟨rfl, source⟩
    change (runAt (TwoAddress.MemRef.lower cells third)
      (TwoAddress.MemRef.evalBody (selectThird f g input x y)) fuel
      (TwoAddress.MemRef.lower cells third).entry .nil middle).map _ = _
    rw [source]
    rfl

private theorem split_pair (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (block : PairBlock cells ambient next scope) (env : Env scope)
    (initial final : Buffer cells) (x y z : Word)
    (success : runAt (lower cells first second third) (evalBody f g input) fuel (pairBlock block) env initial =
      some (some ((pairEnv x y).append (wordEnv z)), final)) :
    ∃ pairFuel thirdFuel middle,
      runAt (Linked.MemRef.lower cells first second) (Linked.MemRef.evalBody f input)
        pairFuel block env initial = some (some (pairEnv x y), middle) ∧
      runAt (TwoAddress.MemRef.lower cells third) (TwoAddress.MemRef.evalBody (selectThird f g input x y))
        thirdFuel (TwoAddress.MemRef.lower cells third).entry .nil middle = some (some (wordEnv z), final) := by
  induction fuel generalizing scope initial with
  | zero => cases success
  | succ fuel ih =>
    rw [pair_run_succ] at success
    cases step : (Block.eval (Linked.MemRef.evalBody f input) block env).run initial with
    | none => rw [step] at success; cases success
    | some evaluated =>
      rw [step] at success
      rcases evaluated with ⟨out, buffer⟩
      cases out with
      | inl frame =>
        obtain ⟨leftFuel, rightFuel, middle, left, right⟩ := ih _ _ buffer success
        exact ⟨leftFuel + 1, rightFuel, middle, by rw [runAt_succ, step]; exact left, right⟩
      | inr values =>
        obtain ⟨rfl, right⟩ := (entry_success first second third f g input values fuel buffer final x y z).mp success
        exact ⟨1, fuel, buffer, by rw [runAt_succ, step]; rfl, right⟩

private theorem join_pair (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (pairFuel thirdFuel : Nat) (block : PairBlock cells ambient next scope) (env : Env scope)
    (initial middle final : Buffer cells) (x y z : Word)
    (left : runAt (Linked.MemRef.lower cells first second) (Linked.MemRef.evalBody f input)
      pairFuel block env initial = some (some (pairEnv x y), middle))
    (right : runAt (TwoAddress.MemRef.lower cells third) (TwoAddress.MemRef.evalBody (selectThird f g input x y))
      thirdFuel (TwoAddress.MemRef.lower cells third).entry .nil middle = some (some (wordEnv z), final)) :
    ∃ fuel, runAt (lower cells first second third) (evalBody f g input) fuel (pairBlock block) env initial =
      some (some ((pairEnv x y).append (wordEnv z)), final) := by
  induction pairFuel generalizing scope initial with
  | zero => cases left
  | succ pairFuel ih =>
    rw [runAt_succ] at left
    cases step : (Block.eval (Linked.MemRef.evalBody f input) block env).run initial with
    | none => rw [step] at left; cases left
    | some evaluated =>
      rw [step] at left
      rcases evaluated with ⟨out, buffer⟩
      cases out with
      | inl frame =>
        obtain ⟨fuel, returned⟩ := ih _ _ buffer left
        exact ⟨fuel + 1, by rw [pair_run_succ, step]; exact returned⟩
      | inr values =>
        change some (some values, buffer) = some (some (pairEnv x y), middle) at left
        cases left
        refine ⟨thirdFuel + 1, ?_⟩
        rw [pair_run_succ, step]
        exact (entry_success first second third f g input (pairEnv x y) thirdFuel middle final x y z).mpr ⟨rfl, right⟩

private theorem decode_success {res : List Width} {A : Type}
    (read : Env res → Buffer cells → A) (values : Env res) (final : Buffer cells)
    (correct : ∀ e b, read e b = read values final ↔ e = values ∧ b = final)
    (raw : Option (Option (Env res) × Buffer cells)) :
    (raw.bind fun (returned, buffer) => returned.map fun env => read env buffer) = some (read values final) ↔
      raw = some (some values, final) := by
  cases raw with
  | none => simp
  | some evaluated =>
    rcases evaluated with ⟨output, buffer⟩
    cases output with
    | none => simp
    | some env => simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq, correct]

private theorem pair_success (first : Graph ambient) (second : Graph next)
    (f : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (initial middle : Buffer cells) (x y : Word) :
    Linked.MemRef.runFuel first second f input fuel initial = some (x, y, middle) ↔
      runAt (Linked.MemRef.lower cells first second) (Linked.MemRef.evalBody f input) fuel
        (Linked.MemRef.lower cells first second).entry .nil initial = some (some (pairEnv x y), middle) := by
  apply decode_success (fun env buffer => (env.get .here, env.get (.there .here), buffer)) (pairEnv x y)
  intro env buffer
  obtain ⟨left, right, rfl⟩ := pair_eta env
  change (left, right, buffer) = (x, y, middle) ↔ pairEnv left right = pairEnv x y ∧ buffer = middle
  constructor
  · intro equal
    cases equal
    exact ⟨rfl, rfl⟩
  · rintro ⟨equal, rfl⟩
    cases equal
    rfl

private theorem third_success (third : Graph last) (input : Tuple (Val cells) last)
    (fuel : Nat) (initial final : Buffer cells) (z : Word) :
    TwoAddress.MemRef.runFuel third input fuel initial = some (z, final) ↔
      runAt (TwoAddress.MemRef.lower cells third) (TwoAddress.MemRef.evalBody input) fuel
        (TwoAddress.MemRef.lower cells third).entry .nil initial = some (some (wordEnv z), final) := by
  apply decode_success (fun env buffer => (env.get .here, buffer)) (wordEnv z)
  intro env buffer
  obtain ⟨word, rfl⟩ := word_eta env
  change (word, buffer) = (z, final) ↔ wordEnv word = wordEnv z ∧ buffer = final
  constructor
  · intro equal
    cases equal
    exact ⟨rfl, rfl⟩
  · rintro ⟨equal, rfl⟩
    cases equal
    rfl

private theorem linked_success (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (fuel : Nat) (initial final : Buffer cells) (x y z : Word) :
    runFuel first second third f g input fuel initial = some (x, y, z, final) ↔
      runAt (lower cells first second third) (evalBody f g input) fuel
        (lower cells first second third).entry .nil initial = some (some ((pairEnv x y).append (wordEnv z)), final) := by
  apply decode_success (fun env buffer => (env.get .here, env.get (.there .here),
    env.get (.there (.there .here)), buffer)) ((pairEnv x y).append (wordEnv z))
  intro env buffer
  obtain ⟨a, b, c, rfl⟩ := triple_eta env
  change (a, b, c, buffer) = (x, y, z, final) ↔
    (pairEnv a b).append (wordEnv c) = (pairEnv x y).append (wordEnv z) ∧ buffer = final
  constructor
  · intro equal
    cases equal
    exact ⟨rfl, rfl⟩
  · rintro ⟨equal, rfl⟩
    cases equal
    rfl

theorem returns_iff_pair_then_third (first : Graph ambient) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring ambient next) (g : Boundary.Wiring next last) (input : Tuple (Val cells) ambient)
    (initial final : Buffer cells) (x y z : Word) :
    (∃ fuel, runFuel first second third f g input fuel initial = some (x, y, z, final)) ↔
      ∃ pairFuel thirdFuel middle,
        Linked.MemRef.runFuel first second f input pairFuel initial = some (x, y, middle) ∧
        TwoAddress.MemRef.runFuel third (selectThird f g input x y) thirdFuel middle = some (z, final) := by
  simp only [linked_success, pair_success, third_success]
  constructor
  · rintro ⟨fuel, returned⟩
    exact split_pair first second third f g input fuel _ _ initial final x y z returned
  · rintro ⟨leftFuel, rightFuel, middle, left, right⟩
    exact join_pair first second third f g input leftFuel rightFuel _ _ initial middle final x y z left right

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Proofs
