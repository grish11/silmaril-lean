module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Thms
import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind

open LetCase.Structural.Finite (Shape)
open LetCase.Structural.Reply (run)
open LetSeq.StraightLine.Structural (Event Log Trace model)
open Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace.Finite (mem_bind)
open Region.Paper.WithComputedCallReturns
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private inductive Op where
  | prepare
  | choose
  | left
  | right
  | finish

private abbrev bit : Shape := .sum .unit .unit
private abbrev rightPayload : Shape := .pair .unit bit
private abbrev X := bit.ty
private abbrev Y := rightPayload.ty
private abbrev S := Ty.coprod X Y
private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil X

private instance : LetCase.Structural.Finite.Signature Op where
  source
    | .left => .pair bit bit
    | .right => .pair rightPayload bit
    | _ => bit
  target
    | .choose => .sum bit rightPayload
    | _ => bit

private def producer : Operand Op β S :=
  ⟨.op .choose (.op .prepare (.bv 0)), .op (.op .bv)⟩

private def left : Operand Op (β.snoc X) X :=
  ⟨.op .left (.pair (.bv 0) (.bv 1)), .op (.pair .bv .bv)⟩

private def right : Operand Op (β.snoc Y) X :=
  ⟨.op .right (.pair (.bv 0) (.bv 1)), .op (.pair .bv .bv)⟩

private abbrev exits : LCtx (Ty Empty) := [X, X]
private theorem outL : At exits 0 X := rfl
private theorem outR : At exits 1 X := rfl

private def original (a : Operand Op β S) : FiniteExit Op exits β :=
  .case a (.br outL left) (.br outR right)

example : ∃ s paths, Schedule [X] s exits paths ∧ CasePaths [.prepare, .choose] [.left] [.right] 0 1 paths ∧
    Eqv false [X] (original producer).toSSA.bindBranchArguments s exits ∧
    Eqv false [X] (.case (.op .choose (.op .prepare (.var 0)))
      ((Code.ofLetCase left.2).guardedSSA 0) ((Code.ofLetCase right.2).guardedSSA 1)) s exits :=
  operand_schedule outL outR producer left right trivial ⟨trivial, trivial⟩ ⟨trivial, trivial⟩

private def scheduledProducer : Region Op :=
  .let₁ (.op .prepare (.var 0)) (.let₁ (.op .choose (.var 0)) (.br 0 (.var 0)))

private def leftArm : Region Op := (Code.br left).guardedSSA 0
private def rightArm : Region Op := (Code.br right).guardedSSA 1

private theorem leftTyped : Region.ValueBranches [X, X] leftArm exits :=
  .let₁ (.op (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))) (.br outL (.var rfl))

private theorem rightTyped : Region.ValueBranches [Y, X] rightArm exits :=
  .let₁ (.op (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))) (.br outR (.var rfl))

private def scheduled : Region Op :=
  .let₁ (.op .prepare (.var 0)) (.let₁ (.op .choose (.var 0))
    (.case (.var 0)
      (.let₁ (.op .left (.pair (.var 0) (.var 3))) (.br 0 (.var 0)))
      (.let₁ (.op .right (.pair (.var 0) (.var 3))) (.br 1 (.var 0)))))

-- Both arms read the fresh payload at zero and the original capture below
-- the two producer reply slots. The output labels have the same payload type.
private theorem scheduled_replay : Schedule [X] scheduled exits [([.prepare, .choose, .left], 0), ([.prepare, .choose, .right], 1)] ∧
    Eqv false [X] (original producer).toSSA.bindBranchArguments scheduled exits := by
  have runProducer : CallSchedule [X] scheduledProducer S [.prepare, .choose] :=
    .call (.var rfl) (.call (.var rfl) (.ret (.var rfl)))
  have step := Step.seq Op.choose (.op (.var (i := 0) rfl) : Tm.HasType [X] (.op Op.prepare (.var 0)) X)
  have ep : Eqv false [X] ((Code.br producer).guardedSSA 0) scheduledProducer [S] :=
    .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inl (.inl (.inl (.inr step))))
  exact ⟨.call (.var rfl) (.call (.var rfl) (.caseVar (slot := 0) rfl
      (.call (.pair (.var (i := 0) rfl) (.var (i := 3) rfl)) (.ret outL (.var rfl)))
      (.call (.pair (.var (i := 0) rfl) (.var (i := 3) rfl)) (.ret outR (.var rfl))))),
    bind_replay (.op (.op (.var rfl))) runProducer.valueBranches ep
      (.refl leftTyped.hasType) (.refl rightTyped.hasType) leftTyped rightTyped⟩

private theorem prepareTyped : Tm.HasType [X] (.op Op.prepare (.var 0)) X :=
  .op (.var (i := 0) rfl)

private def knownLeft : Operand Op β S :=
  ⟨.let₁ (.op .prepare (.bv 0)) (.inl (.bv 0)), .let₁ (.op .bv) (.inl .bv)⟩

private def knownRight : Operand Op β S :=
  ⟨.let₁ (.op .prepare (.bv 0)) (.inr (.pair .unit (.bv 0))), .let₁ (.op .bv) (.inr (.pair .unit .bv))⟩

private theorem known_producer {v : Tm Op} (hv : Tm.BranchValue [X, X] v S) :
    Eqv false [X] ((Region.br 0 (.let₁ (.op .prepare (.var 0)) v)).bindBranchArguments)
      (.let₁ (.op .prepare (.var 0)) (.br 0 v)) [S] := by
  let step := Region.Paper.UnaryReturn.Step.fuse prepareTyped hv.hasType
  have fusion : ConstructorJoin.Eqv false [X]
      (.let₁ (.op .prepare (.var 0)) (.let₁ v (.br 0 (.var 0))))
      ((Region.br 0 (.let₁ (.op .prepare (.var 0)) v)).bindBranchArguments) [S] :=
    .extra step.typed.1 step.typed.2 (.inl (.inl (.inr (.inl step))))
  have beta : Eqv false [X, X] (.let₁ v (.br 0 (.var 0))) (.br 0 v) [S] :=
    .paper (.cfgEta (.native (.letValue hv (.br (ℓ := 0) rfl (.var (i := 0) rfl)))))
  exact (ofProducts (ProductBind.ofPairs (OrderedPairs.ofCalls fusion.symm))).trans
    (.let₁ prepareTyped beta)

private theorem known_case {v : Tm Op} (hv : Tm.BranchValue [X, X] v S) :
    Eqv false [X] (.case (.let₁ (.op .prepare (.var 0)) v) leftArm rightArm)
      (.let₁ (.op .prepare (.var 0)) (.case v (leftArm.renameVars (Silmaril.DeBruijn.lift Nat.succ))
        (rightArm.renameVars (Silmaril.DeBruijn.lift Nat.succ)))) exits :=
  bind_replay (.let₁ prepareTyped hv.hasType) (.let₁ prepareTyped (.br (ℓ := 0) rfl hv))
    (known_producer hv) (.refl leftTyped.hasType) (.refl rightTyped.hasType) leftTyped rightTyped

-- A producer can perform a request before returning a known tag. Both
-- constructor β rules drop the entire unchosen arm at the original exits.
example : Eqv false [X] (original knownLeft).toSSA.bindBranchArguments
    (.let₁ (.op .prepare (.var 0))
      (.let₁ (.op .left (.pair (.var 0) (.var 1))) (.br 0 (.var 0)))) exits := by
  have hl := leftTyped.hasType.renameVars ((Ren.wk [X] X).lift X)
  have hr := rightTyped.hasType.renameVars ((Ren.wk [X] X).lift Y)
  exact (known_case (.inl (.var (i := 0) rfl))).trans
    (.let₁ prepareTyped (constructor_left (.var (i := 0) rfl) hl hr))

example : Eqv false [X] (original knownRight).toSSA.bindBranchArguments
    (.let₁ (.op .prepare (.var 0))
      (.let₁ (.op .right (.pair (.pair .unit (.var 0)) (.var 1))) (.br 1 (.var 0)))) exits := by
  have hl := leftTyped.hasType.renameVars ((Ren.wk [X] X).lift X)
  have hr := rightTyped.hasType.renameVars ((Ren.wk [X] X).lift Y)
  exact (known_case (.inr (.pair .unit (.var (i := 0) rfl)))).trans
    (.let₁ prepareTyped (constructor_right (.pair .unit (.var (i := 0) rfl)) hl hr))

private abbrev V := LetSeq.StraightLine.Structural.Value (α := Empty)
private abbrev eval := (model (α := Empty) (Φ := Op)).eval
private abbrev Output := V (Region.packedExitType exits)

private def dispatch (x : V X) : V S → Trace Empty Op Output
  | .inl payload => eval .left (payload, x) >>= fun reply => pure (.inl reply)
  | .inr payload => eval .right (payload, x) >>= fun reply => pure (.inr (.inl reply))

private theorem pure_step {A B : Type} (x : A) (k : A → Trace Empty Op B) :
    ((pure x : Trace Empty Op A) >>= k) = k x :=
  pure_bind _ _

private theorem assemble {A B : Type} (x : A) (y : B) :
    (do let a ← (pure x : Trace Empty Op A)
        let b ← (pure y : Trace Empty Op B)
        pure (a, b)) = (pure (x, y) : Trace Empty Op (A × B)) :=
  (pure_step x _).trans (pure_step y _)

-- The observation uses the exact finite-exit encoder. It retains distinct
-- output tags and executes only the handler selected by the producer reply.
private theorem run_original (ρ : BoundEnv V β) :
    run (original producer).encode.toLetCase.2 ρ =
      (eval .prepare (ρ 0) >>= fun prepared => eval .choose prepared >>= dispatch (ρ 0)) := by
  simp only [original, FiniteExit.encode, FiniteExit.tag, exits, producer, left, right,
    Code.toLetCase, run, LetCase.LocallyNameless.Derivation.denote]
  have prep : ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) = eval .prepare (ρ 0) :=
    pure_step (ρ 0) _
  erw [prep]
  let start : Trace Empty Op (V X) := eval .prepare (ρ 0)
  erw [← show (start >>= eval .choose >>= dispatch (ρ 0)) =
    (start >>= fun prepared => eval .choose prepared >>= dispatch (ρ 0)) from bind_assoc _ _ _]
  congr 1
  funext packet
  cases packet with
  | inl a =>
    change (((do let l ← (pure a : Trace Empty Op (V X))
                 let x ← (pure (ρ 0) : Trace Empty Op (V X))
                 pure (l, x)) >>= eval .left) >>= fun reply => pure (Sum.inl reply : Output)) =
      dispatch (ρ 0) (.inl a)
    erw [assemble a (ρ 0), dispatch]
    exact congrArg (fun m : Trace Empty Op (V X) => m >>= fun y => pure (Sum.inl y : Output))
      (pure_step (a, ρ 0) (eval .left))
  | inr b =>
    change ((((do let r ← (pure b : Trace Empty Op (V Y))
                  let x ← (pure (ρ 0) : Trace Empty Op (V X))
                  pure (r, x)) >>= eval .right) >>= fun reply =>
      (pure (.inl reply) : Trace Empty Op (V (Ty.coprod X Ty.empty)))) >>= fun reply =>
        pure (Sum.inr reply : Output)) = dispatch (ρ 0) (.inr b)
    erw [assemble b (ρ 0), dispatch]
    trans ((eval .right (b, ρ 0) >>= fun reply =>
      (pure (.inl reply) : Trace Empty Op (V (Ty.coprod X Ty.empty)))) >>= fun reply =>
        pure (Sum.inr reply : Output))
    · congr 2
      exact pure_step (b, ρ 0) (eval .right)
    · exact (bind_assoc _ _ _).trans (by
        congr 1
        funext reply
        exact pure_step (.inl reply : V (Ty.coprod X Ty.empty)) _)

private def event (f : Op) (a : V (instrSrc f)) (b : V (instrTrg f)) : Log Empty Op :=
  FreeMonoid.of (⟨f, a, b⟩ : Event)

-- Both tags are reachable. These observations carry the actual typed input,
-- intermediate reply and selected payload, and have exactly three events.
example (ρ : BoundEnv V β) (prepared payload result : V X) :
    (Sum.inl result, event .prepare (ρ 0) prepared *
      (event .choose prepared (.inl payload) * event .left (payload, ρ 0) result)) ∈
        (run (original producer).encode.toLetCase.2 ρ).outcomes := by
  rw [run_original]
  exact mem_bind.mpr ⟨prepared, _, _, ⟨prepared, rfl⟩,
    mem_bind.mpr ⟨.inl payload, _, _, ⟨.inl payload, rfl⟩,
      mem_bind.mpr ⟨result, _, 1, ⟨result, rfl⟩, rfl, by simp [event]⟩, rfl⟩, rfl⟩

example (ρ : BoundEnv V β) (prepared result : V X) (payload : V Y) :
    (Sum.inr (Sum.inl result), event .prepare (ρ 0) prepared *
      (event .choose prepared (.inr payload) * event .right (payload, ρ 0) result)) ∈
        (run (original producer).encode.toLetCase.2 ρ).outcomes := by
  rw [run_original]
  exact mem_bind.mpr ⟨prepared, _, _, ⟨prepared, rfl⟩,
    mem_bind.mpr ⟨.inr payload, _, _, ⟨.inr payload, rfl⟩,
      mem_bind.mpr ⟨result, _, 1, ⟨result, rfl⟩, rfl, by simp [event]⟩, rfl⟩, rfl⟩

-- Every log follows one route. The tag and its handler agree.
example (ρ : BoundEnv V β) {output : Output} {log : Log Empty Op}
    (h : (output, log) ∈ (run (original producer).encode.toLetCase.2 ρ).outcomes) :
    (∃ value, output = Sum.inl value ∧ log.toList.map Event.generator = [.prepare, .choose, .left]) ∨
    (∃ value, output = Sum.inr (Sum.inl value) ∧ log.toList.map Event.generator = [.prepare, .choose, .right]) := by
  rw [run_original] at h
  obtain ⟨_, _, _, ⟨_, prepared⟩, afterPrepare, rfl⟩ := mem_bind.mp h
  obtain ⟨packet, _, _, ⟨_, chosen⟩, afterChoose, rfl⟩ := mem_bind.mp afterPrepare
  rw [← (Prod.mk.inj prepared).2, ← (Prod.mk.inj chosen).2]
  cases packet with
  | inl payload =>
    obtain ⟨reply, _, tail, ⟨_, handled⟩, finish, rfl⟩ := mem_bind.mp afterChoose
    have done : (output, tail) = (Sum.inl reply, 1) := finish
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj done
    rw [← (Prod.mk.inj handled).2]
    exact .inl ⟨reply, rfl, rfl⟩
  | inr payload =>
    obtain ⟨reply, _, tail, ⟨_, handled⟩, finish, rfl⟩ := mem_bind.mp afterChoose
    have done : (output, tail) = (Sum.inr (Sum.inl reply), 1) := finish
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj done
    rw [← (Prod.mk.inj handled).2]
    exact .inr ⟨reply, rfl, rfl⟩

section Continuation

open Morphism.CaseSSA (erase erase_hasType)

private def caseOperand : Operand Op β X :=
  (Code.case producer (.br left) (.br right)).toLetCase

private def finishOperand : Operand Op β X :=
  ⟨.op .finish caseOperand.1, .op caseOperand.2⟩

private def route : FiniteExit Op exits (β.snoc X) :=
  .case ⟨.bv 0, .bv⟩ (.br outL ⟨.bv 2, .bv⟩) (.br outR ⟨.bv 2, .bv⟩)

private theorem routeSchedule : Schedule [X, X] route.toSSA exits [([], 0), ([], 1)] :=
  .caseVar (slot := 0) rfl (.ret outL (.var (i := 2) rfl)) (.ret outR (.var (i := 2) rfl))

private def source : Region Op :=
  .let₁ (erase finishOperand.1) route.toSSA

-- The scheduled operands keep the inner payload and capture. The later
-- reply selects either original outward label, even though their types agree.
example : ∃ s before, CasePaths [.prepare, .choose] [.left] [.right] 0 0 before ∧
    Schedule [X] s exits (Continuation.callPaths .finish before [([], 0), ([], 1)]) ∧
    Continuation.Eqv false [X] source s exits :=
  Continuation.operand_schedule (f := Op.finish) producer left right trivial ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ routeSchedule

example : ∃ s before, CasePaths [.prepare, .choose] [.left] [.right] 0 0 before ∧
    Schedule [X] s exits (Continuation.callPaths .finish before [([], 1)]) ∧
    Continuation.Eqv false [X] ((Code.ofLetCase finishOperand.2).guardedSSA 1) s exits :=
  Continuation.guarded_operand_schedule (f := Op.finish) outR producer left right trivial
    ⟨trivial, trivial⟩ ⟨trivial, trivial⟩

private def argumentSchedule : Region Op :=
  scheduled.renameLabels (fun _ => 0)

private theorem argumentTyped : Schedule [X] argumentSchedule [X]
    [([.prepare, .choose, .left], 0), ([.prepare, .choose, .right], 0)] :=
  .call (.var rfl) (.call (.var rfl) (.caseVar (slot := 0) rfl
    (.call (.pair (.var (i := 0) rfl) (.var (i := 3) rfl)) (.ret (i := 0) rfl (.var rfl)))
    (.call (.pair (.var (i := 0) rfl) (.var (i := 3) rfl)) (.ret (i := 0) rfl (.var rfl)))))

private def finalSchedule : Region Op :=
  argumentSchedule.lsubst (fun _ => Continuation.invoke .finish route.toSSA)

-- The capture is still present after both reply binders and the terminal case.
example : finalSchedule = .let₁ (.op .prepare (.var 0)) (.let₁ (.op .choose (.var 0))
    (.case (.var 0)
      (.let₁ (.op .left (.pair (.var 0) (.var 3))) (.let₁ (.op .finish (.var 0))
        (.case (.var 0) (.br 0 (.var 6)) (.br 1 (.var 6)))))
      (.let₁ (.op .right (.pair (.var 0) (.var 3))) (.let₁ (.op .finish (.var 0))
        (.case (.var 0) (.br 0 (.var 6)) (.br 1 (.var 6))))))) :=
  rfl

example : Schedule [X] finalSchedule exits
    [([.prepare, .choose, .left, .finish], 0), ([.prepare, .choose, .left, .finish], 1),
      ([.prepare, .choose, .right, .finish], 0), ([.prepare, .choose, .right, .finish], 1)] ∧
    Continuation.Eqv false [X] source finalSchedule exits := by
  have labels : Ren exits [X] (fun _ => 0) := by
    intro i A hi
    have typed : A = X := by simpa [exits] using List.mem_of_getElem? hi
    exact typed ▸ (rfl : At [X] 0 X)
  have ep := scheduled_replay.2.renameLabels labels
  change Eqv false [X]
    (.case (erase producer.1) ((Code.br left).guardedSSA 0) ((Code.br right).guardedSSA 0))
    argumentSchedule [X] at ep
  exact ⟨Continuation.splice (f := Op.finish) argumentTyped routeSchedule,
    Continuation.call_replay (f := Op.finish) (erase_hasType producer.2.toHasType) (erase_hasType left.2.toHasType)
      (erase_hasType right.2.toHasType) routeSchedule.valueBranches.hasType argumentTyped.valueBranches (Continuation.ofSums ep)⟩

private def onArgument (x : V X) : V S → Trace Empty Op (V X)
  | .inl a => eval .left (a, x)
  | .inr b => eval .right (b, x)

private theorem run_argument (ρ : BoundEnv V β) :
    run caseOperand.2 ρ =
      ((eval .prepare (ρ 0) >>= eval .choose) >>= onArgument (ρ 0)) := by
  simp only [caseOperand, producer, left, right, Code.toLetCase, run, LetCase.LocallyNameless.Derivation.denote]
  have prep : ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .prepare) = eval .prepare (ρ 0) :=
    pure_step (ρ 0) _
  erw [prep]
  congr 1
  funext packet
  cases packet with
  | inl a =>
    change ((do let l ← (pure a : Trace Empty Op (V X))
                let x ← (pure (ρ 0) : Trace Empty Op (V X))
                pure (l, x)) >>= eval .left) = eval .left (a, ρ 0)
    erw [assemble a (ρ 0)]
    exact pure_step (a, ρ 0) (eval .left)
  | inr b =>
    change ((do let r ← (pure b : Trace Empty Op (V Y))
                let x ← (pure (ρ 0) : Trace Empty Op (V X))
                pure (r, x)) >>= eval .right) = eval .right (b, ρ 0)
    erw [assemble b (ρ 0)]
    exact pure_step (b, ρ 0) (eval .right)

private def routeTag (x : V X) : V X → Output
  | .inl _ => .inl x
  | .inr _ => .inr (.inl x)

private theorem run_route (ρ : BoundEnv V β) (reply : V X) :
    run route.encode.toLetCase.2 (ρ.snoc reply) = pure (routeTag (ρ 0) reply) := by
  simp only [route, FiniteExit.encode, FiniteExit.tag, exits, Code.toLetCase, run,
    LetCase.LocallyNameless.Derivation.denote]
  refine (pure_step (A := V X) (B := Output) reply _).trans ?_
  cases reply with
  | inl u => exact pure_step (A := V X) (B := Output) (ρ 0) _
  | inr u =>
    change (((pure (ρ 0) : Trace Empty Op (V X)) >>= fun v =>
      (pure (.inl v) : Trace Empty Op (V (Ty.coprod X Ty.empty)))) >>= fun v => pure (Sum.inr v : Output)) = _
    erw [show ((pure (ρ 0) : Trace Empty Op (V X)) >>= fun v =>
      (pure (.inl v) : Trace Empty Op (V (Ty.coprod X Ty.empty)))) = pure (.inl (ρ 0)) from pure_step (ρ 0) _]
    exact pure_step (.inl (ρ 0) : V (Ty.coprod X Ty.empty)) _

private def traceCode : Code Op β (Region.packedExitType exits) :=
  .let₁ finishOperand route.encode

private theorem run_continuation (ρ : BoundEnv V β) :
    run traceCode.toLetCase.2 ρ =
      (eval .prepare (ρ 0) >>= fun prepared => eval .choose prepared >>= fun packet =>
        onArgument (ρ 0) packet >>= fun value => eval .finish value >>= fun reply =>
          pure (routeTag (ρ 0) reply)) := by
  change ((run caseOperand.2 ρ >>= eval .finish) >>= fun reply =>
    run route.encode.toLetCase.2 (ρ.snoc reply)) = _
  have routed : (fun reply : V X => run route.encode.toLetCase.2 (ρ.snoc reply)) =
      fun reply => (pure (routeTag (ρ 0) reply) : Trace Empty Op Output) :=
    funext (run_route ρ)
  erw [run_argument, routed]
  exact (bind_assoc _ _ _).trans ((bind_assoc _ _ _).trans (bind_assoc _ _ _))

private theorem request_event {f : Op} {a : V (instrSrc f)} {b : V (instrTrg f)}
    {k : V (instrTrg f) → Trace Empty Op Output} {y : Output} {tail : Log Empty Op}
    (h : (y, tail) ∈ (k b).outcomes) :
    (y, event f a b * tail) ∈ (eval f a >>= k).outcomes :=
  mem_bind.mpr ⟨b, event f a b, tail, ⟨b, rfl⟩, h, rfl⟩

-- The selected arm's actual reply becomes the later call's argument.
-- The final output returns the original capture at the selected label.
example (ρ : BoundEnv V β) (prepared payload armReply : V X) :
    (Sum.inl (ρ 0), event .prepare (ρ 0) prepared *
      (event .choose prepared (.inl payload) *
        (event .left (payload, ρ 0) armReply * event .finish armReply (.inl PUnit.unit)))) ∈
      (run traceCode.toLetCase.2 ρ).outcomes := by
  rw [run_continuation]
  apply request_event (f := Op.prepare) (b := prepared)
  apply request_event (f := Op.choose) (b := .inl payload)
  apply request_event (f := Op.left) (b := armReply)
  rw [← mul_one (event .finish armReply (.inl PUnit.unit))]
  exact request_event (f := Op.finish) (b := .inl PUnit.unit) rfl

example (ρ : BoundEnv V β) (prepared armReply : V X) (payload : V Y) :
    (Sum.inr (Sum.inl (ρ 0)), event .prepare (ρ 0) prepared *
      (event .choose prepared (.inr payload) *
        (event .right (payload, ρ 0) armReply * event .finish armReply (.inr PUnit.unit)))) ∈
      (run traceCode.toLetCase.2 ρ).outcomes := by
  rw [run_continuation]
  apply request_event (f := Op.prepare) (b := prepared)
  apply request_event (f := Op.choose) (b := .inr payload)
  apply request_event (f := Op.right) (b := armReply)
  rw [← mul_one (event .finish armReply (.inr PUnit.unit))]
  exact request_event (f := Op.finish) (b := .inr PUnit.unit) rfl

private theorem observed_event {f : Op} {a : V (instrSrc f)}
    {k : V (instrTrg f) → Trace Empty Op Output} {y : Output} {log : Log Empty Op}
    (h : (y, log) ∈ (eval f a >>= k).outcomes) :
    ∃ reply tail, (y, tail) ∈ (k reply).outcomes ∧ log = event f a reply * tail := by
  obtain ⟨reply, _, tail, ⟨_, called⟩, rest, rfl⟩ := mem_bind.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj called
  exact ⟨_, tail, rest, rfl⟩

private theorem handler_events (ρ : BoundEnv V β) (f : Op) (a : V (instrSrc f))
    (argument : V (instrTrg f) → V X) {output : Output} {log : Log Empty Op}
    (h : (output, log) ∈ (eval f a >>= fun b =>
      eval .finish (argument b) >>= fun reply => pure (routeTag (ρ 0) reply)).outcomes) :
    log.toList.map Event.generator = [f, .finish] := by
  obtain ⟨_, _, next, rfl⟩ := observed_event h
  obtain ⟨_, tail, done, rfl⟩ := observed_event next
  have pureTrace : (output, tail) = (_, 1) := done
  rw [(Prod.mk.inj pureTrace).2]
  rfl

-- Every successful execution contains the two producer requests, exactly
-- one handler, and exactly one call by the enclosing operand context.
example (ρ : BoundEnv V β) {output : Output} {log : Log Empty Op}
    (h : (output, log) ∈ (run traceCode.toLetCase.2 ρ).outcomes) :
    log.toList.map Event.generator = [.prepare, .choose, .left, .finish] ∨
      log.toList.map Event.generator = [.prepare, .choose, .right, .finish] := by
  rw [run_continuation] at h
  obtain ⟨_, _, afterPrepare, rfl⟩ := observed_event h
  obtain ⟨packet, _, afterChoose, rfl⟩ := observed_event afterPrepare
  cases packet with
  | inl a => exact .inl (congrArg ([Op.prepare, Op.choose] ++ ·) (handler_events ρ Op.left (a, ρ 0) id afterChoose))
  | inr b => exact .inr (congrArg ([Op.prepare, Op.choose] ++ ·) (handler_events ρ Op.right (b, ρ 0) id afterChoose))

end Continuation

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind
