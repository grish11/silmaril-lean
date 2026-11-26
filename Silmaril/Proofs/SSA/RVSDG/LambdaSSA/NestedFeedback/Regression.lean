module

meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Thms
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Defs
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Thms
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Defs
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Thms
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Defs
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered.Thms
import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Thms
meta import Silmaril.SSA.Isotope.Types.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Defs

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Regression

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open TwoBlock.TwoExit (callCase)
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev innerPayload : Ty := .product number number

@[reducible] private def Value : Ty → Type
  | .base _ => Nat
  | .product a b => Value a × Value b
  | .unit => PUnit
  | .coprod a b => Value a ⊕ Value b
  | .empty => PEmpty

private def coerceValue {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerceValue g ∘ coerceValue f
  | .product f g => fun (a,b) => (coerceValue f a, coerceValue g b)
  | .coprod f g => Sum.map (coerceValue f) (coerceValue g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := coerceValue

private inductive Op | enter | inner | finish | tailHeader | tailBody | forkGate
  | routingHeader | routingJoin | consumeBody
  deriving DecidableEq

local instance : HasTy Op Ty :=
  ⟨fun | .inner => innerPayload | _ => number,
   fun | .enter => innerPayload | .inner => .coprod number innerPayload
       | .finish | .tailHeader | .routingJoin => .coprod number number
       | .tailBody | .consumeBody => number
       | .routingHeader => .coprod .unit number
       | .forkGate => .coprod (.coprod number number) number⟩

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private abbrev Runtime := StateT Nat Part
private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .enter, n => StateT.mk fun token => Part.some ((n, (0 : Nat)), 10 * token + 1)
  | .inner, (n, step) => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 99 ∨ (show Nat from step) = 0 then .inr (n, (1 : Nat)) else .inl n,
      10 * token + 2)
  | .finish, n => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 0 then .inr (1 : Nat) else .inl token, 10 * token + 3)
  | .tailHeader, n => StateT.mk fun token =>
    Part.some (.inl ((show Nat from n) + token), 10 * token + 4)
  | .tailBody, n => pure n
  | .routingHeader, n => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 0 then .inl PUnit.unit else .inr n, token + 1)
  | .routingJoin, n => StateT.mk fun token =>
    Part.some (if token = 1 then .inr n else .inl n, token + 1)
  | .consumeBody, n => StateT.mk fun token =>
    if (show Nat from n) = 99 then Part.none else Part.some ((show Nat from n) + token, token + 4)
  | .forkGate, n => pure (if (show Nat from n) = 1 then .inl (.inl (7 : Nat)) else .inr n)

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def op (f : Op) : TwoBlock.Instruction Op (instrSrc (τ := Ty) f) (instrTrg (τ := Ty) f) :=
  ⟨f, rfl, rfl⟩

private def program : Loop Op number innerPayload number number :=
  ⟨op .enter, op .inner, op .finish⟩

private def lowered := lower program
private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)

private theorem call_eq (f : Op) (x : Value (instrSrc f)) :
    TwoBlock.call (ε := Bool) (m := Runtime) (op f) x = instruction f x := by
  unfold TwoBlock.call
  change instruction f x >>= pure = _
  exact bind_pure _

private abbrev innerAction := callCase (ε := Bool) (m := Runtime) program.inner

private theorem inner_step (n step token : Nat) :
    Elgot.StateT.body innerAction ((n,step),token) =
      Part.some (if n = 99 ∨ step = 0 then .inr ((n,1),10 * token + 2) else .inl (n,10 * token + 2)) := by
  have action : innerAction = instruction .inner := by
    funext x
    change callCase (ε := Bool) (m := Runtime) (op .inner) x = instruction .inner x
    unfold callCase
    exact (congrArg (fun (v : Runtime (Value (.coprod number innerPayload))) => v >>= pure)
      (call_eq .inner x)).trans (bind_pure _)
  rw [action]
  by_cases repeatStep : n = 99 ∨ step = 0 <;>
    simp [repeatStep, instruction, Elgot.StateT.body, Elgot.StateT.distribute, Part.pure_eq_some]

private theorem inner_returns (n token : Nat) (allowed : n ≠ 99) :
    (iter innerAction ((n,0) : Value innerPayload)).run token =
      Part.some (n, 100 * token + 22) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.more (a' := ((n,1), 10 * token + 2))
  · rw [inner_step]
    simp
  · apply Elgot.Part.Runs.done
    rw [inner_step]
    simp [allowed]
    omega

private theorem inner_noReturn (step token : Nat) :
    (iter innerAction ((99,step) : Value innerPayload)).run token = Part.none := by
  have impossible {input : (Nat × Nat) × Nat} {out : Nat × Nat}
      (h : Elgot.Part.Runs (Elgot.StateT.body innerAction) input out) : input.1.1 ≠ 99 := by
    induction h with
    | @done current out result =>
      rcases current with ⟨⟨n, step⟩, token⟩
      intro eq
      change n = 99 at eq
      subst n
      rw [inner_step] at result
      simp at result
    | @more current next out result run ih =>
      rcases current with ⟨⟨n, step⟩, token⟩
      intro eq
      change n = 99 at eq
      subst n
      rw [inner_step] at result
      have nextEq : next = ((99,1),10 * token + 2) := by simpa using result
      exact ih (congrArg (fun p : (Nat × Nat) × Nat => p.1.1) nextEq)
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro out h
  exact impossible ((Elgot.Part.mem_iter_iff _ _ _).mp h) rfl

private noncomputable abbrev roundAction := round (ε := Bool) (m := Runtime) program

private theorem round_run (n token : Nat) :
    (roundAction n).run token =
      if n = 99 then Part.none
      else Part.some ((if n = 0 then Sum.inr (1 : Nat) else Sum.inl (1000 * token + 122)),
        10000 * token + 1223) := by
  unfold roundAction round
  rw [show TwoBlock.call (ε := Bool) (m := Runtime) program.enter n =
    instruction .enter n from call_eq .enter _]
  have finish_eq (k : Nat) : callCase (ε := Bool) (m := Runtime) program.finish k = instruction .finish k := by
    unfold callCase
    rw [show TwoBlock.call (ε := Bool) (m := Runtime) program.finish k =
      instruction .finish k from call_eq .finish _]
    exact bind_pure _
  simp only [finish_eq, StateT.run_bind, Part.bind_eq_bind]
  change (((Part.some (((n,0) : Value innerPayload),10 * token + 1)).bind _).bind _) = _
  rw [Part.bind_some]
  change (((iter innerAction ((n,0) : Value innerPayload)).run (10 * token + 1)).bind _) = _
  by_cases blocked : n = 99
  · subst n
    rw [inner_noReturn]
    simp
  · rw [inner_returns _ _ blocked]
    simp only [blocked, ite_false, Part.bind_some]
    have beforeFinish : 100 * (10 * token + 1) + 22 = 1000 * token + 122 := by omega
    rw [beforeFinish]
    have afterFinish : 10 * (1000 * token + 122) + 3 = 10000 * token + 1223 := by omega
    change Part.some ((if n = 0 then Sum.inr (1 : Nat) else Sum.inl (1000 * token + 122)),
      10 * (1000 * token + 122) + 3) = _
    rw [afterFinish]

private theorem returning :
    (iter roundAction (0 : Nat)).run 0 = Part.some ((1223122 : Nat),12231223) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.more (a' := ((1 : Nat),1223))
  · apply Part.eq_some_iff.mp
    unfold Elgot.StateT.body
    simp [round_run, Elgot.StateT.distribute]
  · apply Elgot.Part.Runs.done
    apply Part.eq_some_iff.mp
    unfold Elgot.StateT.body
    simp [round_run, Elgot.StateT.distribute]

private theorem noReturn : (iter roundAction (99 : Nat)).run 0 = Part.none := by
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro out h
  rw [Elgot.Part.mem_iter_iff] at h
  have noStep : Elgot.StateT.body roundAction ((99 : Nat),0) = Part.none := by
    unfold Elgot.StateT.body
    simp [round_run]
  cases h with
  | done h | more h _ => rw [noStep] at h; exact Part.notMem_none _ h

private theorem graph_returns (coherent : Coherent) :
    returns (ε := Bool) lowered.1 (0 : Nat) 0 (1223122 : Nat) 12231223 := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) (1223122 : Nat) 0 12231223).mpr
  rw [show lowered.2.typing = regionTyping program from rfl,
    denote_rounds program coherent (PUnit.unit, (0 : Nat)), StateT.run_bind, returning]
  simp only [StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some]

private theorem graph_undefined (coherent : Coherent) : observe (ε := Bool) lowered.1 (99 : Nat) 0 = Part.none := by
  apply (lowered.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 0).mpr
  rw [show lowered.2.typing = regionTyping program from rfl,
    denote_rounds program coherent (PUnit.unit, (99 : Nat)), StateT.run_bind, noReturn]
  exact Part.bind_none _

private def recovered : Reverse.Fibre lowered.1 :=
  (Reverse.recover lowered.1).get (by
    change (Reverse.recover (graph program)).isSome = true
    rw [Reverse.recover_generated]
    rfl)

example : recovered.source = region program := by
  unfold recovered
  have h : Reverse.recover lowered.1 =
      some ⟨innerPayload, number, region program, lowered.2⟩ := Reverse.recover_generated program
  exact congrArg Reverse.Fibre.source (Option.get_of_eq_some _ h)

example (coherent : Coherent) :
    ((Region.denote (ε := Bool) (m := Runtime) recovered.witness.typing (PUnit.unit, (0 : Nat))).run 0) =
      Part.some (.inl (1223122 : Nat),12231223) :=
  (Reverse.fibre_returns_iff recovered coherent (PUnit.unit, (0 : Nat)) (1223122 : Nat) 0 12231223).mp
    (graph_returns coherent)

example (coherent : Coherent) :
    ((Region.denote (ε := Bool) (m := Runtime) recovered.witness.typing (PUnit.unit, (99 : Nat))).run 0) =
      Part.none :=
  (Reverse.fibre_undefined_iff recovered coherent (PUnit.unit, (99 : Nat)) 0).mp (graph_undefined coherent)

open OrderedTheta (carried)
open OrderedRuntime.Structured (Threaded runtime runtimePort)

private abbrev Boundary := Threaded (carried (Carrier number number))
private abbrev BodyResult := Threaded (OrderedTheta.results (Carrier number number))

private def useEntryToken {past : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    {t : OrderedRuntime.Structured.Ty Ty} (wire : Origin Boundary past t) : Origin Boundary past t :=
  if token : runtime = t then token ▸ (.arg (.tail .head) : Origin Boundary past runtime) else wire

/-- Leave the payload wire from the inner θ in place and substitute the outer
activation's entry token for the token returned by the inner θ. -/
private def staleBody :
    NestedTheta.Term (NestedFeedback.Op Op) Boundary [] (Wiring.BodySigs number innerPayload number number)
      BodyResult :=
  match (Wiring.outerBody program).1 with
  | .bind enter entries (.bind inner children (.bind finish leaf rest)) =>
    let inputs := finish.inputs.map (fun _ wire => useEntryToken wire)
    .bind enter entries (.bind inner children (.bind {finish with inputs} leaf rest))

private def stale : Graph Op number number :=
  let term : NestedTheta.Term (NestedFeedback.Op Op) Boundary [] [Boundary] Boundary :=
    .bind (NestedTheta.ExplicitRuntime.thetaNode (ins := carried (Carrier number number))
      (.arg (runtimePort (carried (Carrier number number)))) (.cons (.arg .head) .nil)
      (Wiring.BodySigs number innerPayload number number)) (fun _ => staleBody)
      (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))
  term.toGraph

private theorem staleParses : Reverse.candidate stale = some ⟨innerPayload, number, program⟩ := by
  have reads : Reverse.read stale = Reverse.read (graph program) := by
    simp only [Reverse.read, stale, graph, NestedTheta.Term.toTerm_toGraph]
    rfl
  unfold Reverse.candidate
  rw [reads]
  exact Reverse.candidate_generated program

private def finishAddresses (g : Graph Op number number) : List Address :=
  match g.toTerm with
  | .bind outer body (.ret _) =>
    (Reverse.readTheta outer.kind body (fun child => match child with
      | .bind _ _ (.bind _ _ (.bind finish _ _)) => some finish.inputs.addresses
      | _ => none)).getD []

private theorem staleDifferent : graph program ≠ stale := by
  intro same
  have addresses := congrArg finishAddresses same
  have correct : finishAddresses (graph program) = [Address.output 1 0, Address.output 1 1] := rfl
  have wrong : finishAddresses stale = [Address.output 1 0, Address.arg 1] := rfl
  rw [correct, wrong] at addresses
  cases addresses

example : Reverse.recognize stale = none :=
  Reverse.reject_wiring ⟨innerPayload, number, program⟩ staleParses staleDifferent

#eval show IO Unit from do
  unless (Reverse.recover lowered.1).isSome do
    throw (IO.userError "could not reverse the nested feedback graph")
  unless (Reverse.candidate stale).isSome && (Reverse.recover stale).isNone do
    throw (IO.userError "the nested feedback recognizer accepted a stale token")

section Composition

open Acyclic.Theta
open Acyclic.Theta.StructuredCFG
open Acyclic.Theta.Sequential

private def tailLoop : Acyclic.Theta.Loop Op number number number number number :=
  ⟨op .tailHeader, .instruction (op .tailBody), op .finish⟩

private def tailNormal : StructuredCFG.Reverse.Normal Op number number number number number number
    [Flat.Serial.WirePorts number number number] := .loop tailLoop

private def composed :=
  WithNestedFeedback.Syntax.link (.nested program) (.structured tailNormal.toSyntax)

private def mixed := WithNestedFeedback.lower composed

private theorem tailReturns (input token : Nat) :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) tailLoop) input).run token =
      Part.some ((.inl (input + token) : LabelDen [number,number]), 10 * token + 4) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  have header : callCase (ε := Bool) (m := Runtime) tailLoop.header input =
      instruction .tailHeader input := by
    unfold callCase
    refine (congrArg (fun (x : Runtime (Value (.coprod number number))) => x >>= pure) ?_).trans
      (bind_pure _)
    exact call_eq .tailHeader _
  simp [Elgot.StateT.body, Elgot.StateT.distribute, ExplicitRuntime.round, header, instruction]

private theorem composedReturns (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) mixed.2.typing (PUnit.unit, (0 : Nat))).run 0 =
      Part.some ((.inl (13454345 : Nat) : LabelDen [number,number]), 122312234) := by
  change (Region.denote (ε := Bool) (m := Runtime)
    (Flat.link (WithNestedFeedback.Leaf.source program) (Flat.Fragment.loop tailLoop)).typing
      (PUnit.unit, (0 : Nat))).run 0 = _
  rw [Flat.denote_link _ _ coherent, StateT.run_bind, WithNestedFeedback.Leaf.source_rounds _ coherent,
    StateT.run_bind, returning]
  simp only [StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some]
  rw [Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent]
  exact tailReturns 1223122 12231223

private theorem composedUndefined (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) mixed.2.typing (PUnit.unit, (99 : Nat))).run 0 = Part.none := by
  change (Region.denote (ε := Bool) (m := Runtime)
    (Flat.link (WithNestedFeedback.Leaf.source program) (Flat.Fragment.loop tailLoop)).typing
      (PUnit.unit, (99 : Nat))).run 0 = _
  rw [Flat.denote_link _ _ coherent, StateT.run_bind, WithNestedFeedback.Leaf.source_rounds _ coherent,
    StateT.run_bind, noReturn]
  simp only [Part.bind_eq_bind, Part.bind_none]

private theorem mixedReturn (coherent : Coherent) :
    Flat.Serial.returns (ε := Bool) mixed.1 (0 : Nat) 0 (.inl (13454345 : Nat)) 122312234 :=
  (mixed.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) (.inl (13454345 : Nat)) 0 122312234).mpr
    (composedReturns coherent)

private theorem mixedUndefined (coherent : Coherent) :
    Flat.Serial.observe (ε := Bool) mixed.1 (99 : Nat) 0 = Part.none :=
  (mixed.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 0).mpr (composedUndefined coherent)

private theorem tailSupported : StructuredCFG.Reverse.Supported tailNormal :=
  .instruction (op .tailBody)

private theorem cutAccepted :
    WithNestedFeedback.Reverse.recover mixed.1 = some ⟨composed.source.region, mixed.2⟩ :=
  WithNestedFeedback.Reverse.recover_generated program tailNormal tailSupported

private def recoveredMixed : WithNestedFeedback.Fibre mixed.1 :=
  (WithNestedFeedback.Reverse.recover mixed.1).get (by rw [cutAccepted]; rfl)

private theorem recoveredAccepted : WithNestedFeedback.Reverse.recover mixed.1 = some recoveredMixed :=
  (Option.some_get _).symm

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredMixed.2.typing (PUnit.unit, (0 : Nat))).run 0 =
      Part.some ((.inl (13454345 : Nat) : LabelDen [number,number]), 122312234) :=
  (WithNestedFeedback.Reverse.recover_returns_iff recoveredAccepted
    coherent (PUnit.unit, (0 : Nat)) _ 0 122312234).mp (mixedReturn coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredMixed.2.typing (PUnit.unit, (99 : Nat))).run 0 = Part.none :=
  (WithNestedFeedback.Reverse.recover_undefined_iff recoveredAccepted
    coherent (PUnit.unit, (99 : Nat)) 0).mp (mixedUndefined coherent)

private abbrev MixedGraph := Flat.Serial.Graph Op number number number number number number
  (Flat.Serial.Joined number number number (WithNestedFeedback.Leaf.Sigs number number)
    [Flat.Serial.WirePorts number number number])

private def staleLinkToken {past : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    {t : OrderedRuntime.Structured.Ty Ty}
    (wire : Origin (Flat.Serial.WirePorts number number number) past t) :
    Origin (Flat.Serial.WirePorts number number number) past t :=
  if token : runtime = t then token ▸ (.arg (.tail .head) :
    Origin (Flat.Serial.WirePorts number number number) past runtime) else wire

private abbrev MixedTerm :=
  NestedTheta.Term (Wires.Op Op) (Flat.Serial.WirePorts number number number) []
    (Flat.Serial.Joined number number number (WithNestedFeedback.Leaf.Sigs number number)
      [Flat.Serial.WirePorts number number number]) (Flat.Serial.WirePorts number number number)

-- Retain the exit adapter's payload. Read the original input token at the
-- connector instead of the token returned by that adapter.
private def staleMixedTerm (term : MixedTerm) : MixedTerm :=
  match term with
  | .bind enter entries (.bind nested body (.bind exit exits (.bind cut children rest))) =>
    let inputs := cut.inputs.map (fun _ wire => staleLinkToken wire)
    .bind enter entries (.bind nested body (.bind exit exits (.bind {cut with inputs} children rest)))

private def staleMixed : MixedGraph := (staleMixedTerm mixed.1.toTerm).toGraph

private theorem staleRead (term : MixedTerm) :
    WithNestedFeedback.Reverse.readTerm (staleMixedTerm term) = WithNestedFeedback.Reverse.readTerm term := by
  cases term with
  | bind _ _ term =>
    cases term with
    | bind _ _ term =>
      cases term with
      | bind _ _ term =>
        cases term with
        | bind cut _ _ => cases cut; rfl

private theorem staleMixedParses : WithNestedFeedback.Reverse.candidate staleMixed = some composed := by
  have same : WithNestedFeedback.Reverse.read staleMixed = WithNestedFeedback.Reverse.read mixed.1 := by
    simp only [WithNestedFeedback.Reverse.read, staleMixed, NestedTheta.Term.toTerm_toGraph, staleRead]
  unfold WithNestedFeedback.Reverse.candidate
  rw [same]
  exact WithNestedFeedback.Reverse.candidate_generated program tailNormal tailSupported

private def cutAddresses (g : MixedGraph) : List Address :=
  match g.toTerm with
  | .bind _ _ (.bind _ _ (.bind _ _ (.bind cut _ _))) => cut.inputs.addresses

example : WithNestedFeedback.Reverse.recover staleMixed = none := by
  apply WithNestedFeedback.Reverse.reject_wiring composed staleMixedParses
  intro eq
  have addresses := congrArg cutAddresses eq
  change [Address.output 2 0, Address.output 2 1] = [Address.output 2 0, Address.arg 1] at addresses
  cases addresses

#eval show IO Unit from do
  unless (WithNestedFeedback.Reverse.recover mixed.1).isSome do
    throw (IO.userError "could not recover the mixed serial graph without supplied views")
  unless (WithNestedFeedback.Reverse.candidate staleMixed).isSome &&
      (WithNestedFeedback.Reverse.recover staleMixed).isNone do
    throw (IO.userError "the mixed serial recognizer failed to certify the cross-cut token")

private def forkGate : TwoBlock.Instruction Op number (StructuredCFG.ChoiceCarrier number number) :=
  op .forkGate

private def forkShape : WithNestedFeedback.Syntax Op number number number number number number
    (StructuredCFG.Selection number number number number ++ [Flat.Serial.WirePorts number number number]) :=
  .branch forkGate (.structured tailNormal.toSyntax) (.nested program) (.structured tailNormal.toSyntax)

private def fork := WithNestedFeedback.lower forkShape

private theorem gateAction (n : Nat) :
    callCase (ε := Bool) (m := Runtime) forkGate n =
      pure (if n = 1 then .inl (.inl (7 : Nat)) else .inr n) := by
  have h : TwoBlock.call (ε := Bool) (m := Runtime) forkGate n = instruction .forkGate n :=
    call_eq .forkGate n
  unfold callCase
  exact (congrArg (fun (x : Runtime (Value (.coprod (.coprod number number) number))) => x >>= pure) h).trans
    (bind_pure _)

private abbrev Exits := LabelDen [number,number]

private theorem fork_run (coherent : Coherent) (n : Nat) :
    Region.denote (ε := Bool) (m := Runtime) fork.2.typing (PUnit.unit,n) =
      (if n = 1 then iter (ExplicitRuntime.round (ε := Bool) tailLoop) (7 : Nat)
       else iter (round (ε := Bool) program) n >>= fun r => pure (Sum.inl r)) >>= fun r : Exits =>
      iter (ExplicitRuntime.round (ε := Bool) tailLoop) (merge r) := by
  change Region.denote (ε := Bool) (m := Runtime)
    (Flat.link (Flat.fork (Flat.Fragment.loop tailLoop) (WithNestedFeedback.Leaf.source program) forkGate)
      (Flat.Fragment.loop tailLoop)).typing (PUnit.unit,n) = _
  rw [Flat.denote_link _ _ coherent, Flat.denote_fork _ _ _ coherent, gateAction]
  by_cases left : n = 1
  · simp only [left, ite_true, pure_bind, Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent]
    rfl
  · simp only [left, ite_false, pure_bind, WithNestedFeedback.Leaf.source_rounds _ coherent,
      Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent]

private theorem forkLeft (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) fork.2.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inl (11 : Nat) : Exits),44) := by
  rw [fork_run coherent]
  simp only [ite_true, StateT.run_bind, Part.bind_eq_bind]
  rw [tailReturns 7 0, Part.bind_some]
  exact tailReturns 7 4

private theorem forkRight (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) fork.2.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl (13454345 : Nat) : Exits),122312234) := by
  rw [fork_run coherent]
  simp only [Nat.zero_ne_one, ite_false, StateT.run_bind, Part.bind_eq_bind, returning,
    StateT.run_pure, Part.pure_eq_some, Part.bind_some]
  exact tailReturns 1223122 12231223

private theorem forkUndefined (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) fork.2.typing (PUnit.unit,(99 : Nat))).run 0 = Part.none := by
  rw [fork_run coherent]
  simp only [show (99 : Nat) ≠ 1 from by decide, ite_false, StateT.run_bind, Part.bind_eq_bind, noReturn, Part.bind_none]

open WithNestedFeedback.Reverse

private theorem forkAccepted : Fork.recover fork.1 = some ⟨forkShape.source.region, fork.2⟩ :=
  Fork.recover_generated forkGate tailNormal program tailNormal tailSupported tailSupported

private def recoveredFork : WithNestedFeedback.Fibre fork.1 :=
  (Fork.recover fork.1).get (by rw [forkAccepted]; rfl)

private theorem recoveredForkAccepted : Fork.recover fork.1 = some recoveredFork :=
  (Option.some_get _).symm

private theorem forkRoundTrip (coherent : Coherent) (input payload token : Nat)
    (h : (Region.denote (ε := Bool) (m := Runtime) fork.2.typing (PUnit.unit,input)).run 0 =
      Part.some ((.inl payload : Exits),token)) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredFork.2.typing (PUnit.unit,input)).run 0 =
      Part.some ((.inl payload : Exits),token) :=
  (Fork.recover_returns_iff recoveredForkAccepted coherent (PUnit.unit,input) (.inl payload) 0 token).mp
    ((fork.2.region_returns_iff coherent (PUnit.unit,input) (.inl payload) 0 token).mpr h)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredFork.2.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inl (11 : Nat) : Exits),44) :=
  forkRoundTrip coherent 1 11 44 (forkLeft coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredFork.2.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl (13454345 : Nat) : Exits),122312234) :=
  forkRoundTrip coherent 0 13454345 122312234 (forkRight coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredFork.2.typing (PUnit.unit,(99 : Nat))).run 0 = Part.none :=
  (Fork.recover_undefined_iff recoveredForkAccepted coherent (PUnit.unit,(99 : Nat)) 0).mp
    ((fork.2.region_undefined_iff coherent (PUnit.unit,(99 : Nat)) 0).mpr (forkUndefined coherent))

private abbrev ForkGraph := Flat.Serial.Graph Op number number number number number number
  (StructuredCFG.Selection number number number number ++ [Flat.Serial.WirePorts number number number])

private abbrev ForkTerm (rest : List (Ports (OrderedRuntime.Structured.Ty Ty)) := []) :=
  NestedTheta.Term (Wires.Op Op) (Flat.Serial.WirePorts number number number) []
    (StructuredCFG.Selection number number number number ++ Flat.Serial.WirePorts number number number :: rest)
    (Flat.Serial.WirePorts number number number)

-- The continuation still reads the selected arm's payload through the γ.
-- Replace its token with the original input token.
private def staleForkTerm {rest : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    (term : ForkTerm rest) : ForkTerm rest :=
  match term with
  | .bind gate op (.bind fork arms (.bind tail body rest)) =>
    let inputs := tail.inputs.map (fun _ wire => staleLinkToken wire)
    .bind gate op (.bind fork arms (.bind {tail with inputs} body rest))

private def staleFork : ForkGraph := (staleForkTerm fork.1.toTerm).toGraph

private theorem staleForkRead (term : ForkTerm) :
    Fork.readFork (staleForkTerm term) = Fork.readFork term := by
  cases term with
  | bind _ _ term =>
    cases term with
    | bind _ _ term =>
      cases term with
      | bind tail _ _ => cases tail; rfl

private theorem staleForkParses : Fork.candidate staleFork = some forkShape := by
  have same : Fork.read staleFork = Fork.read fork.1 := by
    simp only [Fork.read, staleFork, NestedTheta.Term.toTerm_toGraph, staleForkRead]
  unfold Fork.candidate
  rw [same]
  exact Fork.candidate_generated forkGate tailNormal program tailNormal tailSupported tailSupported

private def sharedAddresses (g : ForkGraph) : List Address :=
  match g.toTerm with
  | .bind _ _ (.bind _ _ (.bind tail _ _)) => tail.inputs.addresses

example : Fork.recover staleFork = none := by
  apply Fork.reject_wiring forkShape staleForkParses
  intro eq
  have addresses := congrArg sharedAddresses eq
  change [Address.output 1 0, Address.output 1 1] = [Address.output 1 0, Address.arg 1] at addresses
  cases addresses

#eval show IO Unit from do
  unless (Fork.recover fork.1).isSome do
    throw (IO.userError "could not recover the mixed fork without component views")
  unless (Fork.candidate staleFork).isSome && (Fork.recover staleFork).isNone do
    throw (IO.userError "the mixed fork recognizer failed to certify the shared continuation token")

private def recursiveFork : Recursive.Normal Op number number number number number number
    (StructuredCFG.Selection number number number number ++ [Flat.Serial.WirePorts number number number]) :=
  .fork forkGate (.seq (.localLoop tailLoop) (.leaf (.feedback program))) (.leaf (.feedback program))
    (.leaf (.localLoop tailLoop))

private theorem recursiveSupported : recursiveFork.Supported :=
  ⟨⟨tailSupported, trivial⟩, trivial, tailSupported⟩

private def recursiveGraph := recursiveFork.toSyntax.graph

private theorem recursiveAccepted : Recursive.recover recursiveGraph =
    some ⟨recursiveFork.toSyntax.source.region, .generated recursiveFork.toSyntax⟩ :=
  Recursive.recover_generated recursiveFork recursiveSupported

private def recoveredRecursive : WithNestedFeedback.Fibre recursiveGraph :=
  (Recursive.recover recursiveGraph).get (by rw [recursiveAccepted]; rfl)

private theorem recoveredRecursiveAccepted : Recursive.recover recursiveGraph = some recoveredRecursive :=
  (Option.some_get _).symm

private theorem feedbackReturnsFirstRound (n token : Nat) (nonzero : n ≠ 0) (allowed : n ≠ 99) :
    (iter roundAction n).run token = Part.some (1000 * token + 122, 10000 * token + 1223) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  apply Part.eq_some_iff.mp
  unfold Elgot.StateT.body
  simp [round_run, nonzero, allowed, Elgot.StateT.distribute]

private theorem recursive_run (coherent : Coherent) (n : Nat) :
    Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing (PUnit.unit,n) =
      (if n = 1 then
        iter (ExplicitRuntime.round (ε := Bool) tailLoop) (7 : Nat) >>= fun r => iter roundAction (merge r)
       else iter roundAction n) >>= fun result => iter (ExplicitRuntime.round (ε := Bool) tailLoop) result := by
  change Region.denote (ε := Bool) (m := Runtime)
    (Flat.link (Flat.fork
      (Flat.link (Flat.Fragment.loop tailLoop) (WithNestedFeedback.Leaf.source program))
      (WithNestedFeedback.Leaf.source program) forkGate) (Flat.Fragment.loop tailLoop)).typing
    (PUnit.unit,n) = _
  rw [Flat.denote_link _ _ coherent, Flat.denote_fork _ _ _ coherent, gateAction]
  by_cases left : n = 1 <;>
    simp [left, Flat.denote_link _ _ coherent, Flat.Fragment.loop_denote,
      WithNestedFeedback.Leaf.source_rounds _ coherent, ExplicitRuntime.denote_rounds _ coherent,
      bind_assoc, merge]
  rfl

private theorem recursiveRoundTrip (coherent : Coherent) (input payload token : Nat)
    (h : (Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing (PUnit.unit,input)).run 0 =
      Part.some ((.inl payload : Exits),token)) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRecursive.2.typing (PUnit.unit,input)).run 0 =
      Part.some ((.inl payload : Exits),token) :=
  (Recursive.recover_returns_iff recoveredRecursiveAccepted coherent (PUnit.unit,input) (.inl payload) 0 token).mp
    ((WithNestedFeedback.Related.generated recursiveFork.toSyntax).region_returns_iff
      coherent (PUnit.unit,input) (.inl payload) 0 token |>.mpr h)

private theorem recursiveLeftResult (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing
      (PUnit.unit,(1 : Nat))).run 0 = Part.some ((.inl (45345 : Nat) : Exits),412234) := by
  rw [recursive_run coherent]
  simp only [ite_true, StateT.run_bind, Part.bind_eq_bind, tailReturns 7 0, Part.bind_some]
  change ((iter roundAction (7 : Nat)).run 4).bind _ = _
  rw [feedbackReturnsFirstRound 7 4 (by decide) (by decide), Part.bind_some]
  exact tailReturns 4122 41223

private theorem recursiveRightResult (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing
      (PUnit.unit,(0 : Nat))).run 0 = Part.some ((.inl (13454345 : Nat) : Exits),122312234) := by
  rw [recursive_run coherent]
  simp only [Nat.zero_ne_one, ite_false, StateT.run_bind, Part.bind_eq_bind, returning, Part.bind_some]
  exact tailReturns 1223122 12231223

private theorem recursiveUndefinedResult (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing
      (PUnit.unit,(99 : Nat))).run 0 = Part.none := by
  rw [recursive_run coherent]
  simp only [show (99 : Nat) ≠ 1 from by decide, ite_false, StateT.run_bind,
    Part.bind_eq_bind, noReturn, Part.bind_none]

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRecursive.2.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inl (45345 : Nat) : Exits),412234) :=
  recursiveRoundTrip coherent 1 45345 412234 (recursiveLeftResult coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRecursive.2.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl (13454345 : Nat) : Exits),122312234) :=
  recursiveRoundTrip coherent 0 13454345 122312234 (recursiveRightResult coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRecursive.2.typing (PUnit.unit,(99 : Nat))).run 0 =
      Part.none :=
  (Recursive.recover_undefined_iff recoveredRecursiveAccepted coherent (PUnit.unit,(99 : Nat)) 0).mp
    (((WithNestedFeedback.Related.generated recursiveFork.toSyntax).region_undefined_iff
      coherent (PUnit.unit,(99 : Nat)) 0).mpr (recursiveUndefinedResult coherent))

private def staleRecursive : ForkGraph := (staleForkTerm recursiveGraph.toTerm).toGraph

private theorem staleRecursiveScan (term : ForkTerm) :
    Recursive.scan (staleForkTerm term) = Recursive.scan term := by
  cases term with
  | bind _ _ term =>
    cases term with
    | bind _ _ term =>
      cases term with
      | bind tail _ _ => cases tail; rfl

example : Recursive.recover staleRecursive = none := by
  apply Recursive.reject_wiring recursiveFork
  · simp only [Recursive.candidate, staleRecursive, NestedTheta.Term.toTerm_toGraph, staleRecursiveScan]
    exact Recursive.candidate_generated recursiveFork recursiveSupported
  · intro eq
    have addresses := congrArg sharedAddresses eq
    change [Address.output 1 0, Address.output 1 1] = [Address.output 1 0, Address.arg 1] at addresses
    cases addresses

#eval show IO Unit from do
  unless (Recursive.recover recursiveGraph).isSome do
    throw (IO.userError "could not recover the recursive mixed fork")
  unless (Recursive.candidate staleRecursive).isSome && (Recursive.recover staleRecursive).isNone do
    throw (IO.userError "the recursive mixed recognizer failed to certify the shared continuation token")

open WithNestedFeedback.Normalization

private def unnormalized :=
  WithNestedFeedback.Syntax.link
    (.link recursiveFork.toSyntax (.structured (.loop tailLoop))) (.structured (.loop tailLoop))

-- The two links move inside the fork's existing shared continuation.
example : normalize unnormalized =
    .fork forkGate (.seq (.localLoop tailLoop) (.leaf (.feedback program))) (.leaf (.feedback program))
      (.seq (.localLoop tailLoop) (.seq (.localLoop tailLoop) (.leaf (.localLoop tailLoop)))) := rfl

private def normalizedRecovered : WithNestedFeedback.Fibre (compile unnormalized) :=
  (Recursive.recover (compile unnormalized)).get (compile_recover unnormalized)

private theorem normalizedAccepted : Recursive.recover (compile unnormalized) = some normalizedRecovered :=
  (Option.some_get _).symm

private theorem unnormalized_run (coherent : Coherent) (n : Nat) :
    Region.denote (ε := Bool) (m := Runtime) unnormalized.source.typing (PUnit.unit,n) =
      (do
        let r ← Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing (PUnit.unit,n)
        let next ← iter (ExplicitRuntime.round (ε := Bool) tailLoop) (merge r)
        iter (ExplicitRuntime.round (ε := Bool) tailLoop) (merge next)) := by
  change Region.denote (ε := Bool) (m := Runtime)
    (Flat.link (Flat.link recursiveFork.toSyntax.source (.loop tailLoop)) (.loop tailLoop)).typing
      (PUnit.unit,n) = _
  simp only [Flat.denote_link _ _ coherent, Flat.Fragment.loop_denote,
    ExplicitRuntime.denote_rounds _ coherent, bind_assoc]

private theorem normalizedReturns (coherent : Coherent) (n payload token : Nat)
    (h : (Region.denote (ε := Bool) (m := Runtime) recursiveFork.toSyntax.source.typing (PUnit.unit,n)).run 0 =
      Part.some ((.inl payload : Exits),token)) :
    (Region.denote (ε := Bool) (m := Runtime) normalizedRecovered.2.typing (PUnit.unit,n)).run 0 =
      Part.some ((.inl (payload + token + (10 * token + 4) : Nat) : Exits),10 * (10 * token + 4) + 4) := by
  rw [recover_denote unnormalized normalizedAccepted coherent, unnormalized_run coherent]
  simp only [StateT.run_bind, Part.bind_eq_bind, h, Part.bind_some]
  change ((iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) tailLoop) payload).run token).bind _ = _
  rw [tailReturns payload token, Part.bind_some]
  exact tailReturns (payload + token) (10 * token + 4)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) normalizedRecovered.2.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inl (4579923 : Nat) : Exits),41223444) :=
  normalizedReturns coherent 1 45345 412234 (recursiveLeftResult coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) normalizedRecovered.2.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl (1358888923 : Nat) : Exits),12231223444) :=
  normalizedReturns coherent 0 13454345 122312234 (recursiveRightResult coherent)

private theorem normalizedUndefined (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) normalizedRecovered.2.typing (PUnit.unit,(99 : Nat))).run 0 =
      Part.none := by
  rw [recover_denote unnormalized normalizedAccepted coherent, unnormalized_run coherent]
  simp only [StateT.run_bind, Part.bind_eq_bind, recursiveUndefinedResult coherent, Part.bind_none]

#eval show IO Unit from do
  unless (Recursive.recover (compile unnormalized)).isSome do
    throw (IO.userError "could not recover the normalized mixed source")

private def compiledGraph := compile unnormalized

private def checkedView : Renumbered.View compiledGraph :=
  ⟨_, compiledGraph, NestedTheta.Graph.Isomorphic.refl _⟩

private def recoveredThroughView : Renumbered.Fibre compiledGraph :=
  (Renumbered.recover compiledGraph checkedView).get
    (Renumbered.recover_compiled unnormalized checkedView.numbering)

private theorem viewReturns (coherent : Coherent) (input payload token : Nat)
    (h : (Region.denote (ε := Bool) (m := Runtime) normalizedRecovered.2.typing (PUnit.unit,input)).run 0 =
      Part.some ((.inl payload : Exits),token)) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredThroughView.2.typing (PUnit.unit,input)).run 0 =
      Part.some ((.inl payload : Exits),token) :=
  (recoveredThroughView.2.region_returns_iff coherent (PUnit.unit,input) (.inl payload) 0 token).mp
    ((normalizedRecovered.2.region_returns_iff coherent (PUnit.unit,input) (.inl payload) 0 token).mpr h)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredThroughView.2.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inl (4579923 : Nat) : Exits),41223444) :=
  viewReturns coherent 1 4579923 41223444 (normalizedReturns coherent 1 45345 412234 (recursiveLeftResult coherent))

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredThroughView.2.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl (1358888923 : Nat) : Exits),12231223444) :=
  viewReturns coherent 0 1358888923 12231223444
    (normalizedReturns coherent 0 13454345 122312234 (recursiveRightResult coherent))

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredThroughView.2.typing (PUnit.unit,(99 : Nat))).run 0 =
      Part.none :=
  (recoveredThroughView.2.region_undefined_iff coherent (PUnit.unit,(99 : Nat)) 0).mp
    ((normalizedRecovered.2.region_undefined_iff coherent (PUnit.unit,(99 : Nat)) 0).mpr (normalizedUndefined coherent))

private theorem compiledChains : compiledGraph.ScopeChains := by
  have h := NestedTheta.ExplicitRuntime.EntryChecked.scopeChains (compileChecked unnormalized)
  rw [NestedTheta.Graph.toGraph_toTerm] at h
  exact h

private theorem rejectSwap {V S : Type} {P : Dialect V S}
    {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}
    (g : NestedTheta.Graph P args [] sigs outs) (chain : g.PredecessorChain)
    (a b : Fin sigs.length) (distinct : a ≠ b) :
    ¬ ∀ i, (g.nodes i).inputs.addresses.map (Address.rename (renameVertex (Equiv.swap a b))) =
      (g.nodes (Equiv.swap a b i)).inputs.addresses := by
  intro wires
  have fixed := chain.numbering_fixed (Equiv.swap a b) wires a
  rw [Equiv.swap_apply_left] at fixed
  exact distinct (Fin.ext fixed.symm)

-- A top-level switch and a switch of the first two vertices in the right γ
-- arm would both violate the token dependency.
example : ¬ ∀ i : Fin 7, (compiledGraph.nodes i).inputs.addresses.map
    (Address.rename (renameVertex (Equiv.swap (0 : Fin 7) 1))) =
    (compiledGraph.nodes (Equiv.swap (0 : Fin 7) (1 : Fin 7) i)).inputs.addresses :=
  rejectSwap compiledGraph compiledChains.here (0 : Fin 7) (1 : Fin 7) (by decide)

private def compiledArm := compiledGraph.children (1 : Fin 7) (1 : Fin 2)

example : ¬ ∀ i : Fin 4, (compiledArm.nodes i).inputs.addresses.map
    (Address.rename (renameVertex (Equiv.swap (0 : Fin 4) 1))) =
    (compiledArm.nodes (Equiv.swap (0 : Fin 4) (1 : Fin 4) i)).inputs.addresses :=
  rejectSwap compiledArm (compiledChains.child (1 : Fin 7) (1 : Fin 2)).here
    (0 : Fin 4) (1 : Fin 4) (by decide)

private def staleCompiled := (staleForkTerm compiledGraph.toTerm).toGraph

-- Even a different vertex bijection cannot turn this argument token into the
-- producer's token at the seam.
example : ¬ NestedTheta.Graph.Isomorphic (Wires.Op Op) staleCompiled compiledGraph := by
  intro iso
  have atSeam := iso.inputs_at_rank compiledChains.here (2 : Fin 7) (2 : Fin 7) rfl
  change [Address.output 1 0, Address.arg 1] = [Address.output 1 0, Address.output 1 1] at atSeam
  cases atSeam

#eval show IO Unit from do
  unless (Renumbered.recover compiledGraph checkedView).isSome do
    throw (IO.userError "could not recover a mixed graph through its checked view")

private def routingProducer : Acyclic.Theta.Loop Op number number number .unit number :=
  ⟨op .routingHeader, .instruction (op .tailBody), op .routingJoin⟩

private def routingConsumer : Acyclic.Theta.Loop Op number number number .unit number :=
  ⟨op .routingHeader, .instruction (op .consumeBody), op .finish⟩

private def routed : Flat.Serial.Routed.Source Op number number number number number number .unit number :=
  ⟨routingProducer, routingConsumer⟩

private def wiredRoute := Flat.Serial.Routed.lower routed

private abbrev RoutedExit := LabelDen [(.unit : Ty),number]

private theorem routingCase {X Y : Ty} (p : TwoBlock.Instruction Op number (Silmaril.coprod X Y))
    (input : Nat) :
    callCase (ε := Bool) (m := Runtime) p input = TwoBlock.call (ε := Bool) (m := Runtime) p input := by
  unfold callCase
  exact bind_pure _

private theorem routingBypass :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) routingProducer) (0 : Nat)).run 0 =
      Part.some ((.inl PUnit.unit : RoutedExit), 1) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, ExplicitRuntime.round, routingProducer, routingCase, call_eq,
    instruction, Elgot.StateT.distribute]

private theorem routingProducerReturns (input : Nat) (nonzero : input ≠ 0) :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) routingProducer) input).run 0 =
      Part.some ((.inr (.inl input) : RoutedExit), 4) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  refine .more (a' := (input, 2)) ?_ (.done ?_)
  all_goals
    simp [Elgot.StateT.body, ExplicitRuntime.round, routingProducer,
      ExplicitRuntime.bodyAction, routingCase, call_eq, instruction, Elgot.StateT.distribute, nonzero]

private theorem routingConsumerReturnsAt (input token : Nat) (nonzero : input ≠ 0) (allowed : input ≠ 99) :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) routingConsumer) input).run token =
      Part.some ((.inr (.inl (token + 5)) : RoutedExit), 10 * (token + 5) + 3) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, ExplicitRuntime.round, routingConsumer,
    ExplicitRuntime.bodyAction, routingCase, call_eq, instruction, Elgot.StateT.distribute,
    nonzero, allowed, Nat.add_assoc]

private theorem routingConsumerReturns :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) routingConsumer) (1 : Nat)).run 4 =
      Part.some ((.inr (.inl (9 : Nat)) : RoutedExit), 93) :=
  routingConsumerReturnsAt 1 4 (by decide) (by decide)

private theorem routingConsumerUndefined :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) routingConsumer) (99 : Nat)).run 4 =
      Part.none := by
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro result finite
  rw [Elgot.Part.mem_iter_iff] at finite
  have blocked : Elgot.StateT.body (ExplicitRuntime.round (ε := Bool) (m := Runtime) routingConsumer)
      ((99 : Nat),4) = Part.none := by
    simp [Elgot.StateT.body, ExplicitRuntime.round, routingConsumer,
      ExplicitRuntime.bodyAction, routingCase, call_eq, instruction]
  cases finite with
  | done h | more h _ => rw [blocked] at h; exact Part.notMem_none _ h

private theorem routed_run (coherent : Coherent) (input : Nat) :
    Region.denote (ε := Bool) (m := Runtime) routed.source.typing (PUnit.unit,input) =
      iter (ExplicitRuntime.round (ε := Bool) routingProducer) input >>= fun
        | .inl result => pure (.inl result)
        | .inr (.inl payload) => iter (ExplicitRuntime.round (ε := Bool) routingConsumer) payload
        | .inr (.inr impossible) => nomatch impossible := by
  rw [Flat.Serial.Routed.Source.source, Flat.denote_linkBy _ _ _ coherent]
  simp only [Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent]
  congr 1
  funext exit
  rcases exit with result | payload | impossible
  · rfl
  · rfl
  · exact impossible.elim

-- The unit label skips the consumer. The numeric label enters it after
-- feedback with the exact state returned by the producer.
private theorem routedBypass (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routed.source.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl PUnit.unit : RoutedExit), 1) := by
  rw [routed_run coherent, StateT.run_bind, routingBypass]
  simp only [Part.bind_eq_bind, Part.bind_some, StateT.run_pure, Part.pure_eq_some]

private theorem routedConsumerReturns (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routed.source.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inr (.inl (9 : Nat)) : RoutedExit), 93) := by
  rw [routed_run coherent, StateT.run_bind, routingProducerReturns 1 (by decide)]
  exact (Part.bind_some _ _).trans routingConsumerReturns

private theorem routedConsumerUndefined (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routed.source.typing (PUnit.unit,(99 : Nat))).run 0 =
      Part.none := by
  rw [routed_run coherent, StateT.run_bind, routingProducerReturns 99 (by decide)]
  exact (Part.bind_some _ _).trans routingConsumerUndefined

-- The outputs of the actual numbered graph expose both labels and their
-- differently typed payloads. The second route observes producer feedback.
example (coherent : Coherent) :
    Flat.Serial.returns (ε := Bool) wiredRoute.1 (0 : Nat) 0 (.inl PUnit.unit) 1 :=
  (wiredRoute.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) _ 0 1).mpr (routedBypass coherent)

private theorem routedGraphConsumerReturns (coherent : Coherent) :
    Flat.Serial.returns (ε := Bool) wiredRoute.1 (1 : Nat) 0 (.inr (.inl (9 : Nat))) 93 :=
  (wiredRoute.2.region_returns_iff coherent (PUnit.unit, (1 : Nat)) _ 0 93).mpr (routedConsumerReturns coherent)

example (coherent : Coherent) : Flat.Serial.observe (ε := Bool) wiredRoute.1 (99 : Nat) 0 = Part.none :=
  (wiredRoute.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 0).mpr (routedConsumerUndefined coherent)

open Flat.Serial.Routed.Reverse (CanonicalTerm View Fibre recover complete_generated recognize)

-- Rebuild the table and enter through the checked view API. In this
-- one-token layout, topological positions are forced by dependency.
private def rebuiltRoute := wiredRoute.1.toTerm.toGraph

private def routeView : View rebuiltRoute where
  representative := wiredRoute.1
  numbering := by
    rw [rebuiltRoute, NestedTheta.Graph.toGraph_toTerm]
    exact NestedTheta.Graph.Isomorphic.refl _

private theorem routeChains : wiredRoute.1.ScopeChains := by
  have linked := NestedTheta.ExplicitRuntime.EntryChecked.scopeChains wiredRoute.2.checked
  rw [NestedTheta.Graph.toGraph_toTerm] at linked
  exact linked

example : ¬ ∀ i : Fin 3, (wiredRoute.1.nodes i).inputs.addresses.map
    (Address.rename (renameVertex (Equiv.swap (0 : Fin 3) 1))) =
    (wiredRoute.1.nodes (Equiv.swap (0 : Fin 3) 1 i)).inputs.addresses :=
  rejectSwap wiredRoute.1 routeChains.here (0 : Fin 3) (1 : Fin 3) (by decide)

private def recoveredRoute : Fibre rebuiltRoute :=
  (recover routeView).get (complete_generated routed routeView.numbering)

private theorem recoveredRouteReturns (coherent : Coherent) (input token : Nat) (exit : RoutedExit)
    (h : Flat.Serial.returns (ε := Bool) wiredRoute.1 input 0 exit token) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRoute.2.typing (PUnit.unit,input)).run 0 =
      Part.some (exit, token) :=
  (recoveredRoute.2.region_returns_iff coherent (PUnit.unit,input) exit 0 token).mp
    ((NestedTheta.Partial.returns_iso_iff routeView.numbering (Wires.wireModel (ε := Bool)) _ _).mpr h)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRoute.2.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl PUnit.unit : RoutedExit), 1) :=
  recoveredRouteReturns coherent 0 1 _ <|
    (wiredRoute.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) _ 0 1).mpr (routedBypass coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRoute.2.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inr (.inl (9 : Nat)) : RoutedExit), 93) :=
  recoveredRouteReturns coherent 1 93 _ (routedGraphConsumerReturns coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredRoute.2.typing (PUnit.unit,(99 : Nat))).run 0 =
      Part.none :=
  (recoveredRoute.2.region_undefined_iff coherent (PUnit.unit,(99 : Nat)) 0).mp
    ((NestedTheta.Partial.observe_iso routeView.numbering (Wires.wireModel (ε := Bool)) _).trans
      ((wiredRoute.2.region_undefined_iff coherent (PUnit.unit,(99 : Nat)) 0).mpr
        (routedConsumerUndefined coherent)))

-- Retain the completed payload, but read the original token at the cut.
private def staleRouteTerm (t : CanonicalTerm Op number .unit number number) :
    CanonicalTerm Op number .unit number number :=
  match t with
  | .bind producer body (.bind route children rest) =>
    let inputs := route.inputs.map fun port origin =>
      if h : runtime = port then h ▸ .arg (.tail .head) else origin
    .bind producer body (.bind {route with inputs} children rest)

private def staleRoute := (staleRouteTerm rebuiltRoute.toTerm).toGraph

#eval show IO Unit from do
  unless (recover routeView).isSome && (recognize rebuiltRoute).isSome do
    throw (IO.userError "could not recover the routed γ")
  unless (Flat.Serial.Routed.Reverse.candidate staleRoute).isSome && (recognize staleRoute).isNone do
    throw (IO.userError "the routed γ did not reject a stale token after parsing")

private theorem mixedGraphReturns (coherent : Coherent) :
    Flat.Serial.returns (ε := Bool) compiledGraph (1 : Nat) 0 (.inl (4579923 : Nat)) 41223444 := by
  apply (NestedTheta.Partial.observe_eq_some _ _ _ _).mp
  refine (normalizedRecovered.2.region_observe coherent (PUnit.unit,(1 : Nat)) 0).trans ?_
  exact (congrArg (Part.map (ExplicitRuntime.exitTuple (A := number)))
    (normalizedReturns coherent 1 45345 412234 (recursiveLeftResult coherent))).trans (Part.map_some _ _)

-- Use the same public compile/recover client on both admitted interfaces.
private def translateThenRecover {A X Z L E D : Ty} {sigs : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    (source : Translation.Source Op A X Z L E D sigs) :
    Translation.Fibre source.layout (Translation.compile source) :=
  (Translation.recover source.layout (Translation.compile source)).get (Translation.recover_compiled source)

private theorem translatedReturn {X Z L E D : Ty} {sigs : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    (source : Translation.Source Op number X Z L E D sigs)
    (coherent : Coherent) (exit : LabelDen [E,D]) (token : Nat)
    (expected : Flat.Serial.returns (ε := Bool) (Translation.compile source) (1 : Nat) 0 exit token) :
    (Region.denote (ε := Bool) (m := Runtime) (translateThenRecover source).typing
      (PUnit.unit,(1 : Nat))).run 0 = Part.some (exit,token) := by
  have agrees := Translation.Fibre.region_observe (translateThenRecover source) coherent
    (PUnit.unit,(1 : Nat)) 0
  have output := (NestedTheta.Partial.observe_eq_some _ _ _ _).mpr expected
  have member := Part.eq_some_iff.mp (agrees.symm.trans output)
  rw [Part.mem_map_iff] at member
  obtain ⟨out, finite, equal⟩ := member
  exact Part.eq_some_iff.mpr (ExplicitRuntime.exitTuple_injective equal ▸ finite)


example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime)
      (translateThenRecover (.mixed unnormalized)).typing (PUnit.unit,(1 : Nat))).run 0 =
        Part.some ((.inl (4579923 : Nat) : Exits),41223444) :=
  translatedReturn (.mixed unnormalized) coherent _ 41223444 (mixedGraphReturns coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime)
      (translateThenRecover (.routed routed)).typing (PUnit.unit,(1 : Nat))).run 0 =
        Part.some ((.inr (.inl (9 : Nat)) : RoutedExit),93) :=
  translatedReturn (.routed routed) coherent _ 93 (routedGraphConsumerReturns coherent)

#eval show IO Unit from do
  unless (Translation.recover .mixed (Translation.compile (.mixed unnormalized))).isSome &&
      (Translation.recover .routed (Translation.compile (.routed routed))).isSome do
    throw (IO.userError "the public translation interface did not round trip both layouts")
  unless (Translation.recover .routed staleRoute).isNone do
    throw (IO.userError "the public translation interface accepted a stale routing token")

open OrderedRuntime.Structured (Instruction Values)

private def decideBindDomain {A B : Type} (first : Part A) (rest : A → Part B)
    (domain : Decidable first.Dom) (next : ∀ a, Decidable (rest a).Dom) :
    Decidable (first.bind rest).Dom :=
  match domain with
  | .isFalse absent => .isFalse (fun h => absent h.of_bind)
  | .isTrue present => (present.bind rest).symm ▸ next (first.get present)

private def instructionDomain (op : Op) (input : Value (instrSrc op)) (store : Nat) :
    Decidable ((instruction op input).run store).Dom := by
  cases op <;> simp only [instruction, StateT.run]
  all_goals first | exact .isTrue True.intro | split <;> first | exact .isTrue True.intro | exact .isFalse id

private def wireStepDomain {ins outs : Ports (OrderedRuntime.Structured.Ty Ty)}
    (op : Instruction (TwoBlock.TwoExit.Pure Ty) (Wires.Effect Op) ins outs)
    (input : Tuple (Values (TyDen (τ := Ty))) ins) (store : Nat) :
    Decidable (((Wires.model (Φ := Op) (ε := Bool) (σ := Nat)).step op input).run store).Dom := by
  cases op with
  | pure op => exact .isTrue True.intro
  | effect op =>
    cases op
    case' loop op =>
      cases op
      case' acyclic op => cases op
    case' nested op => cases op
    all_goals
      cases input
      rename_i value tail
      cases tail
      simp only [OrderedRuntime.Structured.Model.step, Wires.model, ExplicitRuntime.orderedModel, NestedFeedback.orderedModel,
        TwoBlock.TwoExit.orderedModel, ExplicitRuntime.readRoute, TwoBlock.call, callCase, StateT.run_bind]
      repeat' first
        | exact .isTrue True.intro
        | exact .isFalse id
        | exact instructionDomain _ _ _
        | (rw [StateT.run_bind])
        | apply decideBindDomain
        | (intro value)
        | (split)

private def wireDomain {ins outs : Ports (OrderedRuntime.Structured.Ty Ty)}
    (op : Wires.Op Op ins outs) (input : Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := Ty)) Nat) ins) :
    Decidable ((Wires.wireModel (ε := Bool)).primitive op input).Dom := by
  cases op with
  | ordered _ _ instr =>
    change Decidable (let (data, token) := OrderedRuntime.Structured.encode input
      (((Wires.model (Φ := Op) (ε := Bool) (σ := Nat)).step instr data).run token).Dom)
    cases OrderedRuntime.Structured.encode input with
    | mk data token => exact wireStepDomain instr data token

private def runnerActions : Translation.Actions (τ := Ty) (ε := Bool) (σ := Nat) Op :=
  NestedTheta.Partial.Executable.Actions.ofDecidable (Wires.wireModel (ε := Bool)) wireDomain

private def operationalSource := Translation.Source.routed routed
private def operationalGraph := Translation.compile operationalSource

example (coherent : Coherent) :
    ∃ fuel, Translation.run runnerActions operationalGraph fuel (1 : Nat) 0 =
      some (ExplicitRuntime.exitTuple (A := number) ((.inr (.inl (9 : Nat)) : RoutedExit), 93)) :=
  (operationalSource.compile_run_iff runnerActions coherent (PUnit.unit,(1 : Nat)) _ 0 93).mpr
    (routedConsumerReturns coherent)

#eval show IO Unit from do
  unless (Translation.run runnerActions operationalGraph 1 (1 : Nat) 0).isNone do
    throw (IO.userError "the routed program skipped producer feedback")
  unless (Translation.run runnerActions operationalGraph 2 (99 : Nat) 0).isNone do
    throw (IO.userError "the selected undefined consumer action returned")
  let output := (Translation.run runnerActions operationalGraph 2 (1 : Nat) 0).map fun result =>
    ((show (PUnit ⊕ Nat) ⊕ Nat from result.get .head), (show Nat from result.get (.tail .head)))
  match output with
  | some (.inl (.inr payload), store) =>
    unless payload == 9 && store == 93 do
      throw (IO.userError "the consumer returned the wrong payload or store")
  | _ => throw (IO.userError "the numbered program did not return at the consumer exit")

open OrderedTheta (point)
open TwoBlock.TwoExit (enter ExitCode Route)
open OrderedRuntime.Structured (Threaded)
open NestedTheta.ExplicitRuntime (ThreadedOp)

private abbrev blockModel := Wires.model (τ := Ty) (Φ := Op) (ε := Bool) (σ := Nat)

-- The path enters the consumer γ arm, its θ body, and the header's body arm.
private def attemptedConsumer :
    NestedTheta.OrderedState.Partial.Block (ThreadedOp (Wires.Effect Op)) (TyDen (τ := Ty)) Nat where
  path := [(2, 1), (0, 0), (1, 1)]
  vertex := 0
  ins := Threaded (carried (Route number .unit number))
  outs := Threaded (carried number)
  opcode := .op (.loop (.acyclic (.call (.right (X := ExitCode .unit number)) (op .consumeBody))))
  input := .cons (.inr (99 : Nat)) (.cons PUnit.unit .nil)
  store := 5

private def blockedEntry := point (enter (A := number) (C := .unit) (D := number) (99 : Nat)) (0 : Nat)

private def producerDone := ExplicitRuntime.exitTuple (A := number)
  ((.inr (.inl (99 : Nat)) : RoutedExit), (4 : Nat))

private theorem producerExec :
    NestedTheta.Partial.exec (Wires.wireModel (ε := Bool))
      (Flat.Serial.Spine.loop routingProducer).code.1 blockedEntry PUnit.unit producerDone := by
  rw [← NestedTheta.Term.toTerm_toGraph (Flat.Serial.Spine.loop routingProducer).code.1]
  apply (NestedTheta.Partial.observe_eq_some _ _ _ _).mp
  change Flat.Serial.observe (ε := Bool) (Flat.Serial.Spine.loop routingProducer).graph (99 : Nat) 0 = _
  rw [Flat.Serial.loop_observe, ExplicitRuntime.graph_observe, routingProducerReturns 99 (by decide)]
  rfl

-- The producer returns after feedback with token 4. The consumer header
-- advances it to 5 and selects the body with payload 99.
private theorem compiledBlock : NestedTheta.ExplicitRuntime.Partial.abnormal blockModel operationalGraph
    blockedEntry (.blocked attemptedConsumer) := by
  change NestedTheta.ExplicitRuntime.Partial.abnormal blockModel routed.code.1.toGraph
    blockedEntry (.blocked attemptedConsumer)
  rw [NestedTheta.ExplicitRuntime.Partial.abnormal, NestedTheta.Term.toTerm_toGraph]
  refine Or.inr ⟨producerDone, ?_, ?_⟩
  · obtain ⟨result, executed, returned⟩ := producerExec
    have repack : point (result.get .head) (result.get (.tail .head)) = result := by
      cases result with
      | cons value tail => cases tail with
        | cons token rest => cases rest; rfl
    change point (result.get .head) (result.get (.tail .head)) = producerDone at returned
    cases repack.symm.trans returned
    exact executed
  · let consumerEntry := point (enter (A := number) (C := .unit) (D := number) (99 : Nat)) (4 : Nat)
    let selected := Tuple.cons (F := OrderedRuntime.Structured.RuntimeValues (TyDen (τ := Ty)) Nat)
      (t := .control 2) ⟨(1 : Fin 2)⟩ consumerEntry
    refine Or.inr ⟨selected, ?_, ?_⟩
    · exact ⟨True.intro, rfl⟩
    apply Or.inl
    apply Or.inl
    apply Or.inl
    refine ⟨consumerEntry, Relation.ReflTransGen.refl, ?_⟩
    let route := point (A := Route number .unit number) (.inr (99 : Nat)) (5 : Nat)
    let header := Tuple.cons (F := OrderedRuntime.Structured.RuntimeValues (TyDen (τ := Ty)) Nat)
      (t := .control 2) ⟨(1 : Fin 2)⟩ route
    refine Or.inr ⟨header, ?_, ?_⟩
    · exact ⟨by repeat' first | exact True.intro | constructor, rfl⟩
    apply Or.inl
    apply Or.inl
    refine ⟨?_, rfl⟩
    change ¬ ((TwoBlock.call (ε := Bool) (m := Runtime) (op .consumeBody) (99 : Nat) >>=
      fun payload => pure (OrderedTheta.pack payload)).run 5).Dom
    simp only [TwoBlock.call, StateT.run_bind, Part.bind_eq_bind]
    intro defined
    exact defined.of_bind.of_bind

example (fuel : Nat) :
    Translation.run runnerActions operationalGraph fuel (99 : Nat) 0 = none :=
  Translation.run_eq_none_of_blocked runnerActions operationalSource.compileChecked compiledBlock fuel

private def mixedConsumer : Recursive.Normal Op number .unit number number .unit number
    (StructuredCFG.Selection number number .unit number ++ [Flat.Serial.WirePorts number .unit number]) :=
  .fork forkGate (.leaf (.feedback program)) (.leaf (.localLoop tailLoop)) (.leaf (.localLoop routingConsumer))

private def routedMixedParts : Flat.Serial.Routed.Mixed.Components Op number .unit number number :=
  ⟨number, number, routingProducer, _, mixedConsumer⟩

private def routedMixedInput :=
  Translation.Source.routedMixed routedMixedParts
    ⟨.instruction _, trivial, tailSupported, .instruction _⟩

private def routedMixedGraph := Translation.compile routedMixedInput

private abbrev mixedResult : RoutedExit := .inr (.inl (41228 : Nat))

private theorem mixedConsumerRun (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) mixedConsumer.toSyntax.source.typing (PUnit.unit,(1 : Nat))).run 4 =
      Part.some (mixedResult, 412283) := by
  change (Region.denote (ε := Bool) (m := Runtime)
    (Flat.link (Flat.fork (WithNestedFeedback.Leaf.source program) (.loop tailLoop) forkGate)
      (.loop routingConsumer)).typing (PUnit.unit,(1 : Nat))).run 4 = _
  rw [Flat.denote_link _ _ coherent, Flat.denote_fork _ _ _ coherent, gateAction, ite_eq_left rfl, pure_bind]
  change ((Region.denote (ε := Bool) (m := Runtime) (WithNestedFeedback.Leaf.source program).typing
    (PUnit.unit,(7 : Nat)) >>= fun (y : Exits) =>
      Region.denote (ε := Bool) (m := Runtime) (Flat.Fragment.loop routingConsumer).typing
        (PUnit.unit, merge y)).run 4) = _
  rw [WithNestedFeedback.Leaf.source_rounds _ coherent]
  simp only [StateT.run_bind, Part.bind_eq_bind, feedbackReturnsFirstRound 7 4 (by decide) (by decide),
    Part.bind_some, StateT.run_pure, Part.pure_eq_some, merge]
  change (Region.denote (ε := Bool) (m := Runtime) (Flat.Fragment.loop routingConsumer).typing
    (PUnit.unit,(4122 : Nat))).run 41223 = _
  rw [Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent]
  exact routingConsumerReturnsAt 4122 41223 (by decide) (by decide)

private theorem routedMixedRun (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routedMixedInput.fragment.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some (mixedResult, 412283) := by
  change (Region.denote (ε := Bool) (m := Runtime)
    (Flat.linkBy (.loop routingProducer) mixedConsumer.toSyntax.source Flat.Serial.Routed.routing).typing
    (PUnit.unit,(1 : Nat))).run 0 = _
  rw [Flat.denote_linkBy _ _ _ coherent, Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent,
    StateT.run_bind, routingProducerReturns 1 (by decide)]
  exact (Part.bind_some _ _).trans (mixedConsumerRun coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) (translateThenRecover routedMixedInput).typing
      (PUnit.unit,(1 : Nat))).run 0 = Part.some (mixedResult, 412283) :=
  ((translateThenRecover routedMixedInput).run_iff runnerActions coherent
    (PUnit.unit,(1 : Nat)) mixedResult 0 412283).mp
    ((routedMixedInput.compile_run_iff runnerActions coherent
      (PUnit.unit,(1 : Nat)) mixedResult 0 412283).mpr (routedMixedRun coherent))

private def staleRoutedMixed := (staleRouteTerm routedMixedGraph.toTerm).toGraph

#eval show IO Unit from do
  unless (Translation.recover routedMixedInput.layout routedMixedGraph).isSome do
    throw (IO.userError "the mixed consumer did not recover from its numbered graph")
  unless (Flat.Serial.Routed.Mixed.candidate staleRoutedMixed).isSome &&
      (Translation.recover routedMixedInput.layout staleRoutedMixed).isNone do
    throw (IO.userError "the mixed consumer did not reject a stale cut token after parsing")
  let output := (Translation.run runnerActions routedMixedGraph 2 (1 : Nat) 0).map fun result =>
    ((show (PUnit ⊕ Nat) ⊕ Nat from result.get .head), (show Nat from result.get (.tail .head)))
  match output with
  | some (.inl (.inr payload), store) =>
    unless payload == 41228 && store == 412283 do
      throw (IO.userError "the routed mixed consumer returned the wrong payload or store")
  | _ => throw (IO.userError "the routed mixed graph did not return at the consumer exit")

end Composition

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Regression
