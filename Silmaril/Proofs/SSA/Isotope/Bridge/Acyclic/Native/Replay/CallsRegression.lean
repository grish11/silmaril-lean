module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Boundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open WithComputedCallReturns
open LetCase.Structural.Finite (Shape)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private inductive Op where
  | dispatch
  | inner
  | middle
  | outer
  | right

private abbrev bit : Shape := .sum .unit .unit
private abbrev X := bit.ty
private abbrev U := (Ty.unit : Ty Empty)
private abbrev β : BoundCtx (Ty Empty) 1 := .snoc .nil X
private abbrev rowInput : BoundCtx (Ty Empty) 2 := β.snoc U

private instance : LetCase.Structural.Finite.Signature Op where
  source _ := bit
  target _ := bit

private def entry : Region Op :=
  .case (.op .dispatch (.var 0)) (.br 0 (.var 0)) (.br 0 .unit)

private theorem entryTyped {A : Ty Empty} : Region.HasType [X] entry [U, A] :=
  .case (.op (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 0) rfl .unit)

-- The incoming unit packet occupies slot zero. The inner call explicitly
-- reads the older captured bit at slot one.
private def operand : Operand Op rowInput X :=
  ⟨.op .outer (.op .middle (.op .inner (.bv 1))), .op (.op (.op .bv))⟩

private def writtenRow : Region Op :=
  .let₁ (.op .outer (.op .middle (.op .inner (.var 1)))) (.br 1 (.var 0))

private def original : Endpoint Op β X :=
  ⟨.cfg entry 1 (fun _ => writtenRow),
    .cfg (fun _ => U) entryTyped
      (fun _ => .let₁ (.op (.op (.op (.var (i := 1) rfl)))) (.br (ℓ := 1) rfl (.var rfl))),
    .join (.case _ (.br _) (.br _)) (.let₁ _ (.br _))⟩

private theorem scheduledOutward {Γ : VCtx (Ty Empty)} {r : Region Op} {fs : List Op} {A : Ty Empty}
    (schedule : CallSchedule Γ r A fs) :
    Outward 1 (r.renameLabels (fun _ => 1)) := by
  induction schedule with
  | ret value => exact .br _
  | call value cont ih => exact .let₁ _ ih

-- Both arms enter the same row. Only that row is rewritten, and the checked
-- schedule records the three distinct call occurrences in execution order.
example : ∃ r : Region Op, CallSchedule [U, X] r X [.inner, .middle, .outer] ∧
    ∃ q : Endpoint Op β X, q.region = .cfg entry 1 (fun _ => r.renameLabels (fun _ => 1)) ∧
      original.CallEqv q ∧ original.Valid q := by
  obtain ⟨r, ordered, replay, _⟩ := operand_schedule false operand trivial
  have renameExit : Ren [X] [U, X] (fun _ => 1) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; rfl
    | succ i => simp [At] at hi
  have block := replay.renameLabels renameExit
  change ConstructorJoin.Eqv false [U, X] writtenRow (r.renameLabels (fun _ => 1)) [U, X] at block
  have rewrite : ConstructorJoin.Eqv false [X] original.region
      (.cfg entry 1 (fun _ => r.renameLabels (fun _ => 1))) [X] :=
    .cfg (fun _ => U) (.refl entryTyped) (fun _ => block)
  let q : Endpoint Op β X :=
    ⟨_, rewrite.typed.2, .join (.case _ (.br _) (.br _)) (scheduledOutward ordered)⟩
  exact ⟨r, ordered, q, rfl, rewrite, Endpoint.call_sound (p := original) (q := q) rewrite⟩

open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Reply (run Γ₀)
open LetSeq.StraightLine.Structural (Trace Event model)
open Isotope.Semantics (BoundEnv)

private abbrev V := LetSeq.StraightLine.Structural.Value (α := Empty)
private abbrev eval := (model (α := Empty) (Φ := Op)).eval

private def entryCode : Code Op β U :=
  .case ⟨.op .dispatch (.bv 0), .op .bv⟩ (.br ⟨.bv 0, .bv⟩) (.br ⟨.unit, .unit⟩)

private def originalCode : Code Op β X :=
  .join entryCode (.let₁ operand (.br ⟨.bv 0, .bv⟩))

example : originalCode.toSSA 0 = original.region := rfl

private def Ordered {A : Type} (ops : List Op) (m : Trace Empty Op A) : Prop :=
  ∀ {x w}, (x, w) ∈ m.outcomes → w.toList.map Event.generator = ops

private theorem ordered_pure {A : Type} (x : A) : Ordered [] (pure x) := by
  intro y w h
  have eq : (y, w) = (x, 1) := h
  rw [(Prod.mk.inj eq).2]
  rfl

private theorem ordered_call (f : Op) (x : V X) : Ordered [f] (eval f x) := by
  intro y w h
  obtain ⟨reply, equal⟩ := h
  rw [← (Prod.mk.inj equal).2]
  rfl

private theorem ordered_bind {A B : Type} {first rest : List Op} {m : Trace Empty Op A}
    {k : A → Trace Empty Op B} (a : Ordered first m) (b : ∀ x, Ordered rest (k x)) :
    Ordered (first ++ rest) (m >>= k) := by
  intro x w hw
  obtain ⟨reply, l, r, hl, hr, rfl⟩ := Silmaril.Semantics.NondeterministicTrace.Finite.mem_bind.mp hw
  change (l.toList ++ r.toList).map Event.generator = first ++ rest
  rw [List.map_append, a hl, b reply hr]

private theorem entry_order (ρ : BoundEnv V β) : Ordered [.dispatch] (run entryCode.toLetCase.2 ρ) := by
  simp only [entryCode, Code.toLetCase, run, Derivation.denote]
  change Ordered [.dispatch] (((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .dispatch) >>= _)
  rw [show ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .dispatch) =
    eval .dispatch (ρ 0) from pure_bind _ _]
  apply ordered_bind (first := [.dispatch]) (rest := []) (ordered_call .dispatch _)
  intro x
  cases x <;> exact ordered_pure _

private theorem row_order (x : V X) :
    Ordered [.inner, .middle, .outer] (((eval .inner x) >>= eval .middle) >>= eval .outer) :=
  ordered_bind (first := [.inner, .middle]) (rest := [.outer])
    (ordered_bind (first := [.inner]) (rest := [.middle]) (ordered_call .inner x) (ordered_call .middle))
    (ordered_call .outer)

-- The actual typed compilation of the written CFG records dispatch before
-- the three row calls for every captured bit and either dispatch reply.
example (ρ : BoundEnv V β) :
    Ordered [.dispatch, .inner, .middle, .outer] (run originalCode.toLetCase.2 ρ) := by
  change Ordered [.dispatch, .inner, .middle, .outer] (run entryCode.toLetCase.2 ρ >>= fun _ =>
    (((((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .inner) >>= eval .middle) >>= eval .outer) >>= pure))
  rw [show ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .inner) =
    eval .inner (ρ 0) from pure_bind _ _]
  simp only [bind_pure]
  exact ordered_bind (first := [.dispatch]) (rest := [.inner, .middle, .outer])
    (entry_order ρ) (fun _ => row_order (ρ 0))

private abbrev Packet := Ty.product X X

-- The shared row uses the captured bit in both operands, including under
-- the left result binder when the right call is scheduled.
private def pairOperand : Operand Op rowInput Packet :=
  ⟨.pair operand.1 (.op .right (.bv 1)), .pair operand.2 (.op .bv)⟩

private def pairCode : Code Op β Packet :=
  .join entryCode (.let₁ pairOperand (.br ⟨.bv 0, .bv⟩))

private def pairEndpoint : Endpoint Op β Packet :=
  ⟨pairCode.toSSA 0,
    .cfg (fun _ => U) entryTyped
      (fun _ => .let₁ (.pair (.op (.op (.op (.var (i := 1) rfl)))) (.op (.var (i := 1) rfl)))
        (.br (ℓ := 1) rfl (.var rfl))),
    .join (.case _ (.br _) (.br _)) (.let₁ _ (.br _))⟩

example : ∃ r : Region Op, CallSchedule [U, X] r Packet [.inner, .middle, .outer, .right] ∧
    ∃ q : Endpoint Op β Packet,
      q.region = .cfg entry 1 (fun _ => r.renameLabels (fun _ => 1)) ∧
      pairEndpoint.PairCallEqv q ∧ pairEndpoint.Valid q := by
  obtain ⟨r, ordered, replay, _⟩ := operand_pair_schedule false pairOperand ⟨trivial, trivial⟩
  have renameExit : Ren [Packet] [U, Packet] (fun _ => 1) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; rfl
    | succ i => simp [At] at hi
  have rewrite : OrderedPairs.Eqv false [X] pairEndpoint.region
      (.cfg entry 1 (fun _ => r.renameLabels (fun _ => 1))) [Packet] :=
    .cfg (fun _ => U) (.refl entryTyped) (fun _ => replay.renameLabels renameExit)
  let q : Endpoint Op β Packet :=
    ⟨_, rewrite.typed.2, .join (.case _ (.br _) (.br _)) (scheduledOutward ordered)⟩
  exact ⟨r, ordered, q, rfl, rewrite, Endpoint.pair_call_sound (p := pairEndpoint) (q := q) rewrite⟩

private def pairObservation (ρ : BoundEnv V β) : Trace Empty Op (V Packet) :=
  run entryCode.toLetCase.2 ρ >>= fun _ =>
    (((eval .inner (ρ 0) >>= eval .middle) >>= eval .outer) >>= fun l =>
      eval .right (ρ 0) >>= fun r => pure (l, r))

-- The actual compiled CFG retains the original capture for the right call
-- and returns the left and right replies in their original positions.
private theorem pair_observation (ρ : BoundEnv V β) :
    run pairCode.toLetCase.2 ρ = pairObservation ρ := by
  change (run entryCode.toLetCase.2 ρ >>= fun _ =>
    (((((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .inner) >>= eval .middle) >>= eval .outer) >>=
      fun l => ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval .right) >>= fun r => pure (l, r)) >>= pure) =
    pairObservation ρ
  have call (f : Op) : ((pure (ρ 0) : Trace Empty Op (V X)) >>= eval f) =
      eval f (ρ 0) := pure_bind _ _
  rw [call, call, bind_pure]
  rfl

example (ρ : BoundEnv V β) :
    Ordered [.dispatch, .inner, .middle, .outer, .right] (run pairCode.toLetCase.2 ρ) := by
  rw [pair_observation]
  apply ordered_bind (first := [.dispatch]) (rest := [.inner, .middle, .outer, .right]) (entry_order ρ)
  intro packet
  apply ordered_bind (first := [.inner, .middle, .outer]) (rest := [.right]) (row_order (ρ 0))
  intro l
  exact ordered_bind (first := [.right]) (rest := []) (ordered_call .right (ρ 0)) (fun r => ordered_pure (l, r))

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
