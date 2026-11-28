module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Thms
import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind

open LetCase.Structural.Finite (Shape)
open LetCase.Structural.Reply (run)
open LetSeq.StraightLine.Structural (Event Log Trace model)
open Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace.Finite (mem_bind)
open Region.Paper.WithComputedCallReturns
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private inductive Op where
  | prepare
  | produce
  | consume
  | right

private abbrev bit : Shape := .sum .unit .unit
private abbrev rightField : Shape := .pair .unit bit
private abbrev X := bit.ty
private abbrev Y := rightField.ty
private abbrev P := Ty.product X Y
private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil X
private abbrev γ := (β.snoc X).snoc Y

private instance : LetCase.Structural.Finite.Signature Op where
  source
    | .consume => .pair bit (.pair rightField bit)
    | _ => bit
  target
    | .produce => .pair bit rightField
    | .right => rightField
    | _ => bit

private def producer : Operand Op β P :=
  ⟨.op .produce (.op .prepare (.bv 0)), .op (.op .bv)⟩

private def pairProducer : Operand Op β P :=
  ⟨.pair (.op .prepare (.bv 0)) (.op .right (.bv 0)), .pair (.op .bv) (.op .bv)⟩

private def consume : Operand Op γ X :=
  ⟨.op .consume (.pair (.bv 1) (.pair (.bv 0) (.bv 2))), .op (.pair .bv (.pair .bv .bv))⟩

private def written (p : Operand Op β P) : Code Op β X :=
  .let₂ p (.let₁ consume (.br ⟨.bv 0, .bv⟩))

private abbrev exits : LCtx (Ty Empty) := [X, X]
private theorem second : At exits 1 X := rfl

-- The two exit payload types coincide. Both checked equations still use
-- exit one at the written and reified native endpoints.
example : ∃ s, Schedule [X] s exits [.prepare, .produce, .consume] ∧
    Eqv false [X] ((written producer).toSSA 1) s exits ∧
    Eqv false [X] ((Code.ofLetCase (.let₂ producer.2 consume.2)).guardedSSA 1) s exits :=
  operand_schedule second producer consume trivial ⟨trivial, trivial, trivial⟩

example : ∃ s, Schedule [X] s exits [.prepare, .right, .consume] ∧
    Eqv false [X] ((written pairProducer).toSSA 1) s exits ∧
    Eqv false [X] ((Code.ofLetCase (.let₂ pairProducer.2 consume.2)).guardedSSA 1) s exits :=
  operand_schedule second pairProducer consume ⟨trivial, trivial⟩ ⟨trivial, trivial, trivial⟩

private def scheduledProducer : Region Op :=
  .let₁ (.op .prepare (.var 0)) (.let₁ (.op .produce (.var 0)) (.br 0 (.var 0)))

private def scheduled : Region Op :=
  .let₁ (.op .prepare (.var 0)) (.let₁ (.op .produce (.var 0))
    (.let₂ (.var 0)
      (.let₁ (.op .consume (.pair (.var 1) (.pair (.var 0) (.var 4))))
        (.br 1 (.var 0)))))

private def consumer : Region Op := (.br consume : Code Op γ X).guardedSSA 1

-- The exact scheduled region keeps the left field at one, the right at
-- zero, and the original capture below the producer's two fresh replies.
example : Schedule [X] scheduled exits [.prepare, .produce, .consume] ∧
    Eqv false [X] ((written producer).toSSA 1) scheduled exits := by
  have runProducer : CallSchedule [X] scheduledProducer P [.prepare, .produce] :=
    .call (.var rfl) (.call (.var rfl) (.ret (.var rfl)))
  have step := Step.seq Op.produce (.op (.var (i := 0) rfl) : Tm.HasType [X] (.op Op.prepare (.var 0)) X)
  have ep : Eqv false [X] ((Code.br producer).guardedSSA 0) scheduledProducer [P] :=
    .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inl (.inl (.inr step)))
  have ec : Schedule [Y, X, X] consumer exits [.consume] :=
    .call (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl)))
      (.ret second (.var rfl))
  exact ⟨.call (.var rfl) (.call (.var rfl) (.unpackVar (i := 0) rfl
      (.call (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 4) rfl)))
        (.ret second (.var rfl))))),
    bind_replay (.op (.op (.var rfl))) runProducer.valueBranches ep
      (Region.Paper.Extension.Eqv.refl ec.valueBranches.hasType)⟩

private abbrev V := LetSeq.StraightLine.Structural.Value (α := Empty)
private abbrev eval := (model (α := Empty) (Φ := Op)).eval

-- In the concrete observation the original input is the argument of
-- prepare, while consume sees the two produced fields and that same input.
-- The monadic expression has one occurrence of each reached request.
private theorem run_written (ρ : BoundEnv V β) :
    run (written producer).toLetCase.2 ρ =
      ((eval .prepare (ρ 0) >>= eval .produce) >>= fun ab =>
        eval .consume (ab.1, (ab.2, ρ 0))) := by
  change (((((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) >>= eval .produce) >>=
    fun ab => ((do
      let l ← (pure ab.1 : Trace Empty Op (V X))
      let rest ← (do
        let r ← (pure ab.2 : Trace Empty Op (V Y))
        let x ← (pure (ρ 0) : Trace Empty Op (V X))
        pure (r, x) : Trace Empty Op (V (Ty.product Y X)))
      pure (l, rest) : Trace Empty Op (V (instrSrc Op.consume))) >>= eval .consume) >>= pure)) = _
  have pure_step {A B : Type} (x : A) (k : A → Trace Empty Op B) :
      ((pure x : Trace Empty Op A) >>= k) = k x := pure_bind _ _
  simp only [pure_step, bind_assoc, bind_pure]
  rw [show ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) =
    eval .prepare (ρ 0) from pure_bind _ _]
  congr 1
  funext ab
  exact (pure_step (A := V X) (B := V X) (ρ 0) _).trans
    ((pure_step (A := V (Ty.product Y X)) (B := V X) (ab.2, ρ 0) _).trans
      (pure_step (ab.1, (ab.2, ρ 0)) (eval .consume)))

example (ρ : BoundEnv V β) {result : V X} {log : Log Empty Op}
    (observed : (result, log) ∈ (run (written producer).toLetCase.2 ρ).outcomes) :
    log.toList.map Event.generator = [.prepare, .produce, .consume] := by
  have sequence :
      ((eval .prepare (ρ 0) >>= eval .produce) >>= fun ab => eval .consume (ab.1, (ab.2, ρ 0))) =
        (eval .prepare (ρ 0) >>= fun prepared =>
          eval .produce prepared >>= fun ab => eval .consume (ab.1, (ab.2, ρ 0))) :=
    bind_assoc _ _ _
  rw [run_written, sequence] at observed
  obtain ⟨_, _, _, ⟨_, prepareEvent⟩, afterPrepare, rfl⟩ := mem_bind.mp observed
  obtain ⟨_, _, _, ⟨_, produceEvent⟩, afterProduce, rfl⟩ := mem_bind.mp afterPrepare
  obtain ⟨_, consumeEvent⟩ := afterProduce
  rw [← (Prod.mk.inj prepareEvent).2, ← (Prod.mk.inj produceEvent).2, ← (Prod.mk.inj consumeEvent).2]
  rfl

section Recursive

private abbrev Argument := instrSrc (τ := Ty Empty) Op.consume
private abbrev Packed := Region.packedExitType exits

private def fields : Operand Op γ Argument :=
  ⟨.pair (.bv 1) (.pair (.bv 0) (.bv 2)), .pair .bv (.pair .bv .bv)⟩

private def nestedCall : Operand Op β X :=
  ⟨.op .consume (.let₂ producer.1 fields.1), .op (.let₂ producer.2 fields.2)⟩

private def routed : FiniteExit Op exits β :=
  .case nestedCall (.br (rfl : At exits 0 X) ⟨.bv 1, .bv⟩) (.br second ⟨.bv 1, .bv⟩)

private def packed : Operand Op β Packed := routed.encode.toLetCase

-- The original packed case has a call whose operand is a product
-- destructure. The original and its actual reification use one schedule
-- at native label one, even with the same payload type at label zero.
example : ∃ s, ∃ paths : List (List Op),
    SumBind.Schedule [X] s [Packed, Packed] (paths.map fun requests => (requests, 1)) ∧
    SumBind.Continuation.Eqv false [X] ((Code.br packed).guardedSSA 1) s [Packed, Packed] ∧
    SumBind.Continuation.Eqv false [X] ((Code.ofLetCase packed.2).guardedSSA 1) s [Packed, Packed] :=
  SumBind.Recursive.normalize (rfl : At [Packed, Packed] 1 Packed) packed
    ⟨⟨trivial, ⟨trivial, trivial, trivial⟩⟩, trivial, trivial⟩

private theorem pure_step {A B : Type} (x : A) (k : A → Trace Empty Op B) :
    ((pure x : Trace Empty Op A) >>= k) = k x :=
  pure_bind _ _

private theorem run_fields (ρ : BoundEnv V β) (ab : V P) :
    run fields.2 ((ρ.snoc ab.1).snoc ab.2) = pure (ab.1, (ab.2, ρ 0)) := by
  change ((pure ab.1 : Trace Empty Op (V X)) >>= fun left =>
    ((pure ab.2 : Trace Empty Op (V Y)) >>= fun right =>
      (pure (ρ 0) : Trace Empty Op (V X)) >>= fun capture => pure (right, capture)) >>= fun rest =>
      (pure (left, rest) : Trace Empty Op (V Argument))) = _
  rw [pure_step ab.1]
  have rest : ((pure ab.2 : Trace Empty Op (V Y)) >>= fun right =>
      (pure (ρ 0) : Trace Empty Op (V X)) >>= fun capture => pure (right, capture)) =
      (pure (ab.2, ρ 0) : Trace Empty Op (V (Ty.product Y X))) :=
    (pure_step ab.2 _).trans (pure_step (A := V X) (ρ 0) _)
  rw [rest]
  exact pure_step (ab.2, ρ 0) _

private theorem run_nested (ρ : BoundEnv V β) :
    run nestedCall.2 ρ =
      ((eval .prepare (ρ 0) >>= eval .produce) >>= fun ab => eval .consume (ab.1, (ab.2, ρ 0))) := by
  have expose : run nestedCall.2 ρ =
      (((((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) >>= eval .produce) >>= fun ab : V P =>
        run fields.2 ((ρ.snoc ab.1).snoc ab.2)) >>= eval .consume) := rfl
  have fieldReturn : (fun ab : V P => run fields.2 ((ρ.snoc ab.1).snoc ab.2)) =
      fun ab => (pure (ab.1, (ab.2, ρ 0)) : Trace Empty Op (V Argument)) :=
    funext (run_fields ρ)
  rw [expose, fieldReturn]
  erw [show ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) =
    eval .prepare (ρ 0) from pure_step (A := V X) (ρ 0) _]
  exact (bind_assoc _ _ _).trans (congrArg (fun k => (eval .prepare (ρ 0) >>= eval .produce) >>= k)
    (funext fun ab : V P => pure_step (ab.1, (ab.2, ρ 0)) (eval .consume)))

private def route (capture : V X) : V X → V Packed
  | .inl _ => .inl capture
  | .inr _ => .inr (.inl capture)

private theorem run_packed (ρ : BoundEnv V β) :
    run packed.2 ρ = (eval .prepare (ρ 0) >>= fun prepared => eval .produce prepared >>= fun ab =>
      eval .consume (ab.1, (ab.2, ρ 0)) >>= fun reply => pure (route (ρ 0) reply)) := by
  have expose : run packed.2 ρ = (run nestedCall.2 ρ >>= fun reply : V X =>
      match reply with
      | .inl _ => (pure (ρ 0) : Trace Empty Op (V X)) >>= fun value => pure (Sum.inl value : V Packed)
      | .inr _ => (((pure (ρ 0) : Trace Empty Op (V X)) >>= fun value =>
          (pure (Sum.inl value) : Trace Empty Op (V (Ty.coprod X Ty.empty)))) >>= fun value =>
            pure (Sum.inr value : V Packed))) := by
    simp only [packed, routed, FiniteExit.encode, FiniteExit.tag, Code.toLetCase, nestedCall, run,
      LetCase.LocallyNameless.Derivation.denote]
    congr 1
    funext reply
    cases reply <;> rfl
  have routing : (fun reply : V X => match reply with
      | .inl _ => (pure (ρ 0) : Trace Empty Op (V X)) >>= fun value => pure (Sum.inl value : V Packed)
      | .inr _ => (((pure (ρ 0) : Trace Empty Op (V X)) >>= fun value =>
          (pure (Sum.inl value) : Trace Empty Op (V (Ty.coprod X Ty.empty)))) >>= fun value =>
            pure (Sum.inr value : V Packed))) = fun reply => pure (route (ρ 0) reply) := by
    funext reply
    cases reply with
    | inl _ => exact pure_step (A := V X) (ρ 0) _
    | inr _ =>
      exact (congrArg (fun m : Trace Empty Op (V (Ty.coprod X Ty.empty)) =>
        m >>= fun value => (pure (Sum.inr value) : Trace Empty Op (V Packed)))
        (pure_step (A := V X) (ρ 0) _)).trans (pure_step _ _)
  rw [expose]
  erw [routing]
  erw [run_nested]
  exact (bind_assoc _ _ _).trans (bind_assoc _ _ _)

private def event (f : Op) (a : V (instrSrc f)) (b : V (instrTrg f)) : Log Empty Op :=
  FreeMonoid.of (⟨f, a, b⟩ : Event)

-- Both consume replies are reachable. The left and right fields are in
-- their original positions, followed by the capture in the call argument.
example (ρ : BoundEnv V β) (prepared reply : V X) (ab : V P) :
    (route (ρ 0) reply, event .prepare (ρ 0) prepared * (event .produce prepared ab *
      event .consume (ab.1, (ab.2, ρ 0)) reply)) ∈ (run packed.2 ρ).outcomes := by
  rw [run_packed]
  exact mem_bind.mpr ⟨prepared, _, _, ⟨prepared, rfl⟩,
    mem_bind.mpr ⟨ab, _, _, ⟨ab, rfl⟩,
      mem_bind.mpr ⟨reply, _, 1, ⟨reply, rfl⟩, rfl, by rw [mul_one]; rfl⟩, rfl⟩, rfl⟩

-- The selected ordered exit is distinct even when its payload is the same.
example (capture : V X) :
    route capture (.inl PUnit.unit) = .inl capture ∧
      route capture (.inr PUnit.unit) = .inr (.inl capture) := ⟨rfl, rfl⟩

example (ρ : BoundEnv V β) {output : V Packed} {log : Log Empty Op}
    (h : (output, log) ∈ (run packed.2 ρ).outcomes) :
    log.toList.map Event.generator = [.prepare, .produce, .consume] := by
  rw [run_packed] at h
  obtain ⟨_, _, _, ⟨_, first⟩, afterPrepare, rfl⟩ := mem_bind.mp h
  obtain ⟨_, _, _, ⟨_, pairReply⟩, afterProduce, rfl⟩ := mem_bind.mp afterPrepare
  obtain ⟨reply, _, tail, ⟨_, consumed⟩, finished, rfl⟩ := mem_bind.mp afterProduce
  have ret : (output, tail) = (route (ρ 0) reply, 1) := finished
  rw [← (Prod.mk.inj first).2, ← (Prod.mk.inj pairReply).2, ← (Prod.mk.inj consumed).2, (Prod.mk.inj ret).2]
  rfl

end Recursive

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind
