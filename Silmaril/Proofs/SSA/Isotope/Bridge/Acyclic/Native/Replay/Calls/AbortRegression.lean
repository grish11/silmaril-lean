module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms
import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind

open LetCase.Structural.Reply (run)
open LetSeq.StraightLine.Structural (Event Log Trace model)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open LambdaSSA.Semantics.Categorical (denoteRegion)
open Morphism.CaseSSA (erase)
open Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace.Finite (mem_bind)
open scoped LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Op where
  | prepare | emptyReply | tail | keep

private abbrev One := (Ty.unit : Ty Empty)
private abbrev Bit := Ty.coprod One One

private instance : HasTy Op (Ty Empty) where
  src _ := Bit
  trg
    | .emptyReply => Ty.empty
    | _ => Bit

private abbrev β : BoundCtx (Ty Empty) 2 := (BoundCtx.nil.snoc Bit).snoc Bit
private abbrev arm := β.snoc One

-- The older capture is at slot two after the branch payload. The empty
-- producer receives the reply of prepare. Tail is in expression position
-- after the abort and therefore has no possible argument.
private def produceEmpty : Operand Op arm Ty.empty :=
  ⟨.op .emptyReply (.op .prepare (.bv 2)), .op (.op .bv)⟩

private def blocked : Operand Op arm Bit :=
  ⟨.op .tail (.abort produceEmpty.1), .op (.abort produceEmpty.2)⟩

private def live : Operand Op arm Bit :=
  ⟨.op .keep (.bv 2), .op .bv⟩

private abbrev exits : LCtx (Ty Empty) := [Bit, Bit]
private theorem exitDead : At exits 0 Bit := rfl
private theorem exitLive : At exits 1 Bit := rfl

private def routed : FiniteExit Op exits β :=
  .case ⟨.bv 0, .bv⟩ (.br exitDead blocked) (.br exitLive live)

private abbrev Packed := Region.packedExitType exits
private def packed : Operand Op β Packed := routed.encode.toLetCase
private theorem packedOut : At [Packed, Packed] 1 Packed := rfl

-- The effectful empty producer has no returning path when eliminated.
example : ∃ s, Schedule arm.toList s exits [] ∧
    Continuation.Eqv false arm.toList ((Code.br ⟨.abort produceEmpty.1, .abort (C := Bit) produceEmpty.2⟩).guardedSSA 0)
      s exits ∧
    Continuation.Eqv false arm.toList ((Code.ofLetCase (.abort (C := Bit) produceEmpty.2)).guardedSSA 0) s exits :=
  Recursive.normalize_abort exitDead produceEmpty trivial

private theorem packed_schedule : ∃ s, ∃ paths : List (List Op),
    Schedule β.toList s [Packed, Packed] (paths.map fun requests => (requests, 1)) ∧
    Continuation.Eqv false β.toList ((Code.br packed).guardedSSA 1) s [Packed, Packed] ∧
    Continuation.Eqv false β.toList ((Code.ofLetCase packed.2).guardedSSA 1) s [Packed, Packed] :=
  Recursive.normalize packedOut packed ⟨trivial, trivial, trivial⟩

-- Compare the literal and reified native arrows at the actual ordered
-- interface, using the same coherent trace model as the observation below.
example :
    let := traceInstructions (α := Empty) (Φ := Op)
    denoteRegion (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
        ((Code.br packed).guardedSSA_valueBranches packedOut).hasType =
      denoteRegion (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
        ((Code.ofLetCase packed.2).guardedSSA_valueBranches packedOut).hasType := by
  let := traceInstructions (α := Empty) (Φ := Op)
  let := trace_region_coherent (Φ := Op)
  obtain ⟨_, _, _, literal, reified⟩ := packed_schedule
  exact Continuation.sound (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
    (fun _ _ => ⟨rfl, rfl⟩) (literal.trans reified.symm) _ _

private abbrev V := LetSeq.StraightLine.Structural.Value (α := Empty)
private abbrev eval := (model (α := Empty) (Φ := Op)).eval

private def input (capture test : V Bit) : BoundEnv V β :=
  let emptyEnv : BoundEnv V .nil := fun i => i.elim0
  (emptyEnv.snoc (A := Bit) capture).snoc (A := Bit) test

private theorem pure_step {A B : Type} (x : A) (k : A → Trace Empty Op B) :
    ((pure x : Trace Empty Op A) >>= k) = k x :=
  pure_bind _ _

-- The free trace model records returned values with their logs. The empty
-- type has no returned value, so even an effectful empty prefix cannot
-- contribute an outcome to the following bind.
private theorem empty_bind {A : Type} (m : Trace Empty Op (V Ty.empty))
    (k : V Ty.empty → Trace Empty Op A) : (m >>= k).outcomes = ∅ := by
  ext outcome
  constructor
  · rcases outcome with ⟨value, log⟩
    intro h
    obtain ⟨impossible, _⟩ := mem_bind.mp h
    exact impossible.elim
  · exact False.elim

private def deadArm : Operand Op arm Packed := FiniteExit.tag exits 0 exitDead blocked
private def liveArm : Operand Op arm Packed := FiniteExit.tag exits 1 exitLive live

private theorem run_dispatch (ρ : BoundEnv V β) :
    run packed.2 ρ = ((pure (ρ 0) : Trace Empty Op (V Bit)) >>= fun test =>
      match test with
      | .inl a => run deadArm.2 (ρ.snoc (A := One) a)
      | .inr b => run liveArm.2 (ρ.snoc (A := One) b)) := by
  simp only [packed, routed, FiniteExit.encode, Code.toLetCase, deadArm, liveArm, run,
    LetCase.LocallyNameless.Derivation.denote]
  congr 1
  funext test
  cases test <;> rfl

private theorem run_dead (capture : V Bit) :
    (run packed.2 (input capture (Sum.inl PUnit.unit))).outcomes = ∅ := by
  let ρ := input capture (.inl PUnit.unit)
  have select : run packed.2 ρ = run deadArm.2 (ρ.snoc (A := One) PUnit.unit) :=
    (run_dispatch ρ).trans (pure_step (A := V Bit) (.inl PUnit.unit) _)
  change (run packed.2 ρ).outcomes = _
  rw [select]
  let env := ρ.snoc (A := One) PUnit.unit
  let eliminate : V Ty.empty → Trace Empty Op (V Bit) := fun z => z.elim
  let tag : V Bit → Trace Empty Op (V Packed) := fun value => pure (.inl value)
  change (((run produceEmpty.2 env >>= eliminate) >>= eval .tail) >>= tag).outcomes = ∅
  erw [bind_assoc (run produceEmpty.2 env >>= eliminate) (eval .tail) tag,
    bind_assoc (run produceEmpty.2 env) eliminate]
  exact empty_bind _ _

private theorem run_live (capture : V Bit) :
    run packed.2 (input capture (Sum.inr PUnit.unit)) =
      (eval .keep capture >>= fun reply => pure (.inr (.inl reply) : V Packed)) := by
  let ρ := input capture (.inr PUnit.unit)
  have select : run packed.2 ρ = run liveArm.2 (ρ.snoc (A := One) PUnit.unit) :=
    (run_dispatch ρ).trans (pure_step (A := V Bit) (.inr PUnit.unit) _)
  change run packed.2 ρ = _
  rw [select]
  change ((((pure capture : Trace Empty Op (V Bit)) >>= eval .keep) >>= fun reply =>
      (pure (.inl reply) : Trace Empty Op (V (Ty.coprod Bit Ty.empty)))) >>= fun value =>
        (pure (.inr value) : Trace Empty Op (V Packed))) = _
  erw [pure_step capture (eval .keep)]
  exact (bind_assoc _ _ _).trans (congrArg (fun k => eval .keep capture >>= k)
    (funext fun reply : V Bit => pure_step (.inl reply : V (Ty.coprod Bit Ty.empty)) _))

private def event (f : Op) (a : V (instrSrc f)) (b : V (instrTrg f)) : Log Empty Op :=
  FreeMonoid.of (⟨f, a, b⟩ : Event)

-- The prepare prefix alone has a typed trace. Once asked for an empty
-- reply, the full left arm has no trace or exit, including the later tail.
-- Every successful observation uses the other original exit position.
example (capture prepared : V Bit) :
    (prepared, event .prepare capture prepared) ∈ (eval .prepare capture).outcomes ∧
      (run packed.2 (input capture (.inl PUnit.unit))).outcomes = ∅ ∧
      (run packed.2 (input capture (.inr PUnit.unit))).outcomes =
        {observed | ∃ reply : V Bit,
          observed = (Sum.inr (Sum.inl reply), event .keep capture reply)} := by
  refine ⟨⟨prepared, rfl⟩, run_dead capture, ?_⟩
  rw [run_live]
  ext ⟨output, log⟩
  constructor
  · intro h
    obtain ⟨reply, _, tail, ⟨_, called⟩, finished, rfl⟩ := mem_bind.mp h
    have done : (output, tail) = (Sum.inr (Sum.inl reply), 1) := finished
    refine ⟨reply, Prod.ext (Prod.mk.inj done).1 ?_⟩
    rw [← (Prod.mk.inj called).2, (Prod.mk.inj called).1, (Prod.mk.inj done).2, mul_one]
    rfl
  · intro h
    obtain ⟨reply, selected⟩ := h
    rw [selected]
    exact mem_bind.mpr ⟨reply, _, 1, ⟨reply, rfl⟩, rfl, by rw [mul_one]; rfl⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind
