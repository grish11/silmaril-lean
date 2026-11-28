module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Reverse (CheckedTable)
open Isotope.Semantics (BoundEnv InstructionModel)
open LetCase.Structural.Finite (Context Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Op | ask

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev Bit := bitShape.ty
private abbrev captures : Context 1 := .snoc .nil Bit
private abbrev exits : LCtx Types := [.unit, .unit]
private abbrev Packet := packedExitType exits
private abbrev Source := captures.snoc Packet

local instance : LetCase.Structural.Finite.Signature Op where
  source _ := .pair bitShape bitShape
  target _ := bitShape

private theorem input : StructuralContext captures := .snoc .nil bitShape
private theorem nonempty : exits ≠ [] := List.cons_ne_nil _ _

private abbrev Val := Ty.denote (fun x : Empty => (x.elim : Type 1))

/-- One request carries the older capture and the input tag. Its reply is a bit. -/
private inductive Event : Type → Type where
  | ask (capture tag : Bool) : Event Bool

private def bit : Val Bit → Bool
  | .inl _ => false
  | .inr _ => true

private def ofBool : Bool → Val Bit
  | false => .inl PUnit.unit
  | true => .inr PUnit.unit

private def instructions : InstructionModel Val Op (Tree Event) :=
  ⟨fun _ arg => vis (.ask (bit arg.1) (bit arg.2)) (fun reply => pure (ofBool reply))⟩

/-- The reply is the current state, and each exchange flips the state. -/
private def policy : Handler Bool Event
  | ⟨_, .ask _ _⟩, state, reply, next => reply = state ∧ next = !state

/-- Ask with the older capture and the input tag, then leave by the exit
named by the reply. Both exits carry a unit payload. -/
private def route : Operand Op Source Packet :=
  ⟨.let₁ (.op .ask (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inl .bv) (.inr (.inl .bv)))⟩

private def tagOf : Val Packet → Bool
  | .inl _ => false
  | .inr _ => true

private def packet : Bool → Val Packet
  | false => .inl PUnit.unit
  | true => .inr (.inl PUnit.unit)

private def stage (capture : Val Bit) (x : Val Packet) : Tree Event (Val (wrap captures Packet)) :=
  vis (.ask (bit capture) (tagOf x)) (fun reply => ret (capture, packet reply))

private abbrev Packed := Val (wrap captures Packet)

private theorem leave_low (capture : Val Bit) {t : Tree Event (Val Packet)}
    (computed : t = ((pure PUnit.unit : Tree Event (Val Ty.unit)) >>= fun a =>
      (pure (Sum.inl a) : Tree Event (Val Packet)))) :
    (t >>= fun y => (pure (capture, y) : Tree Event Packed)) = ret (capture, packet false) := by
  subst computed
  simp only [pure_bind]
  rfl

private theorem leave_high (capture : Val Bit) {t : Tree Event (Val Packet)}
    (computed : t = (((pure PUnit.unit : Tree Event (Val Ty.unit)) >>= fun a =>
      (pure (Sum.inl a) : Tree Event (Val (packedExitType [Ty.unit])))) >>= fun b =>
      (pure (Sum.inr b) : Tree Event (Val Packet)))) :
    (t >>= fun y => (pure (capture, y) : Tree Event Packed)) = ret (capture, packet true) := by
  subst computed
  simp only [pure_bind]
  rfl

/-- The packed term makes one request naming the older capture and the
input tag, and returns the capture beside the exit named by the reply. -/
private theorem run_route (capture : Val Bit) (x : Val Packet) :
    (pack captures route).run instructions (capture, x) = stage capture x := by
  refine (run_pack (M := instructions) captures route
    (BoundEnv.snoc (β := .nil) (fun i => i.elim0) capture) x).trans ?_
  simp only [route, Derivation.denote]
  cases x
  · erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    simp only [instructions]
    erw [vis_bind, vis_bind]
    refine congrArg (vis (Event.ask (bit capture) false)) (funext fun reply => ?_)
    cases reply <;> erw [pure_bind, pure_bind]
    · exact leave_low capture rfl
    · exact leave_high capture rfl
  · erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    simp only [instructions]
    erw [pure_bind, vis_bind, vis_bind]
    refine congrArg (vis (Event.ask (bit capture) true)) (funext fun reply => ?_)
    cases reply <;> erw [pure_bind, pure_bind]
    · exact leave_low capture rfl
    · exact leave_high capture rfl

private theorem tagOf_packet (reply : Bool) : tagOf (packet reply) = reply := by cases reply <;> rfl

/-- Two packed stages: the second request repeats the same older capture
and names the first reply as its input tag. -/
private def twice (capture : Val Bit) (x : Val Packet) : Tree Event Packed :=
  vis (.ask (bit capture) (tagOf x)) fun first =>
    vis (.ask (bit capture) first) fun second => ret (capture, packet second)

private theorem run_twice (capture : Val Bit) (x : Val Packet) :
    (pack captures (Case.seq route route)).run instructions (capture, x) = twice capture x := by
  have stages : (pack captures route).run instructions = fun w => stage w.1 w.2 :=
    funext fun w => run_route w.1 w.2
  rw [run_pack_seq, stages]
  simp only [stage, vis_bind]
  refine congrArg (vis (Event.ask (bit capture) (tagOf x))) (funext fun first => ?_)
  erw [pure_bind]
  rw [tagOf_packet]

/-! ## The functor on the captured term -/

private def native : Case.Interface Op captures input := ⟨exits, nonempty⟩
private def term (a : Operand Op Source Packet) : native ⟶ native := Quotient.mk _ a

private abbrev semantics := handledFunctor instructions policy input

/-- The older capture is carried beside the packed exits. -/
example : (semantics.obj native).ty = .product Bit Packet := rfl

example : semantics.map (term route) = HandledTrace.Arrow.ofProgram (pack captures route) := rfl

example : semantics.map (𝟙 native) = 𝟙 (semantics.obj native) := semantics.map_id native

example : semantics.map (term route ≫ term route) = semantics.map (term route) ≫ semantics.map (term route) :=
  semantics.map_comp (term route) (term route)

/-- The composite class is represented by the packed literal let. -/
example : semantics.map (term route ≫ term route) =
    HandledTrace.Arrow.ofProgram (pack captures (Case.seq route route)) := rfl

/-! ## Observations under the state-dependent policy -/

private theorem packet_injective {a b : Bool} (same : packet a = packet b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases same

/-- The pending request is observable in every state. It names the older
capture and the input tag. -/
example (state : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTrace policy state ((pack captures route).run instructions (capture, x))
      (.request (.ask (bit capture) (tagOf x))) := by
  rw [run_route]
  exact ⟨hasTrace_vis_request _ _, trivial⟩

/-- A completed exchange is admitted exactly when the reply is the current
state. The return keeps the capture and leaves by the exit named by the reply. -/
private theorem stage_result (state reply exit : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTrace policy state ((pack captures route).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) reply (.result (capture, packet exit))) ↔
      reply = state ∧ exit = reply := by
  rw [run_route]
  constructor
  · intro seen
    obtain ⟨_, admitted, _⟩ := seen.2
    have returned : out (ret (capture, packet reply) : Tree Event Packed) =
        Part.some (.ret (capture, packet exit)) := (hasTrace_vis_exchange_iff _ _ _ _).mp seen.1
    rw [out_ret] at returned
    have pair := Visible.ret.inj (Part.some_injective returned)
    exact ⟨admitted.1, (packet_injective (congrArg Prod.snd pair)).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _), ⟨!exit, ⟨rfl, rfl⟩, trivial⟩⟩

/-- The two exits carry the same unit payload and are told apart by the
handler state alone. -/
example (capture : Val Bit) (x : Val Packet) :
    HandledTrace policy false ((pack captures route).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) false (.result (capture, .inl PUnit.unit))) ∧
    HandledTrace policy true ((pack captures route).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) true (.result (capture, .inr (.inl PUnit.unit)))) ∧
    ¬ HandledTrace policy false ((pack captures route).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) false (.result (capture, .inr (.inl PUnit.unit)))) :=
  ⟨(stage_result false false false capture x).mpr ⟨rfl, rfl⟩,
    (stage_result true true true capture x).mpr ⟨rfl, rfl⟩,
    fun seen => Bool.noConfusion ((stage_result false false true capture x).mp seen).2⟩

/-- In the composite the first exchange flips the state, so the second
reply and the final exit are the opposite bit. The second request still
names the same older capture. -/
example (state : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTrace policy state ((pack captures (Case.seq route route)).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) state
        (.exchange (.ask (bit capture) state) (!state) (.result (capture, packet (!state))))) := by
  rw [run_twice]
  exact ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr ((hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _)),
    ⟨!state, ⟨rfl, rfl⟩, ⟨!!state, ⟨rfl, rfl⟩, trivial⟩⟩⟩

/-- The same reply twice is rejected by the policy at the second exchange. -/
example (state : Bool) (capture : Val Bit) (x : Val Packet) (tail : Trace Event Packed) :
    ¬ HandledTrace policy state ((pack captures (Case.seq route route)).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) state (.exchange (.ask (bit capture) state) state tail)) := by
  rintro ⟨_, _, first, _, second, _⟩
  have flipped : state = !state := by rw [first.2] at second; exact second.1
  cases state <;> cases flipped

/-! ## One fixed policy does not separate all native classes -/

/-- Ask with the older capture and the input tag, ignore the reply, and
leave by the exit opposite to the input tag. -/
private def echo : Operand Op Source Packet :=
  ⟨.let₁ (.op .ask (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 1) (.inr (.inl .unit)) (.inl .unit)),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inr (.inl .unit)) (.inl .unit))⟩

private theorem run_echo (capture : Val Bit) (x : Val Packet) :
    (pack captures echo).run instructions (capture, x) =
      vis (.ask (bit capture) (tagOf x)) (fun _ => ret (capture, packet (!tagOf x))) := by
  refine (run_pack (M := instructions) captures echo
    (BoundEnv.snoc (β := .nil) (fun i => i.elim0) capture) x).trans ?_
  simp only [echo, Derivation.denote]
  cases x
  · erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    simp only [instructions]
    erw [vis_bind, vis_bind]
    refine congrArg (vis (Event.ask (bit capture) false)) (funext fun reply => ?_)
    erw [pure_bind, pure_bind]
    exact leave_high capture rfl
  · erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    simp only [instructions]
    erw [pure_bind, vis_bind, vis_bind]
    refine congrArg (vis (Event.ask (bit capture) true)) (funext fun reply => ?_)
    erw [pure_bind, pure_bind]
    exact leave_low capture rfl

/-- Two requests, leaving by the exit opposite to the first reply. -/
private def crossed (capture : Val Bit) (x : Val Packet) : Tree Event Packed :=
  vis (.ask (bit capture) (tagOf x)) fun first =>
    vis (.ask (bit capture) first) fun _ => ret (capture, packet (!first))

private theorem run_crossed (capture : Val Bit) (x : Val Packet) :
    (pack captures (Case.seq route echo)).run instructions (capture, x) = crossed capture x := by
  have second : (pack captures echo).run instructions = fun w =>
      vis (.ask (bit w.1) (tagOf w.2)) (fun _ => ret (w.1, packet (!tagOf w.2))) :=
    funext fun w => run_echo w.1 w.2
  rw [run_pack_seq, run_route, second]
  simp only [stage, vis_bind]
  refine congrArg (vis (Event.ask (bit capture) (tagOf x))) (funext fun first => ?_)
  erw [pure_bind]
  rw [tagOf_packet]

/-- Handled inclusion below a common request needs the continuations only
at replies the policy admits. -/
private theorem handled_vis {R : Type} (e : Event R) {k l : R → Tree Event Packed} (state : Bool)
    (admitted : ∀ reply next, policy ⟨R, e⟩ state reply next → HandledTraceLE policy next (k reply) (l reply)) :
    HandledTraceLE policy state (vis e k) (vis e l) := by
  rintro trace ⟨seen, replay⟩
  cases trace with
  | «prefix» => exact ⟨trivial, trivial⟩
  | request d => exact ⟨(hasTrace_vis_request_iff e l d).mpr ((hasTrace_vis_request_iff e k d).mp seen), trivial⟩
  | result value =>
    have returned : out (vis e k) = Part.some (.ret value) := seen
    rw [out_vis] at returned
    cases Part.some_injective returned
  | exchange d reply tail =>
    obtain ⟨sameType, sameEvent, inner⟩ := (hasTrace_vis_exchange e k d reply tail).mp seen
    subst sameType
    subst sameEvent
    obtain ⟨next, step, rest⟩ := replay
    have below := admitted reply next step tail ⟨inner, rest⟩
    exact ⟨(hasTrace_vis_exchange_iff d l reply tail).mpr below.1, next, step, below.2⟩

/-- The policy never repeats a reply, so it cannot tell the second reply
from the opposite of the first. -/
private theorem twice_equiv_crossed (state : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTraceLE policy state (twice capture x) (crossed capture x) ∧
      HandledTraceLE policy state (crossed capture x) (twice capture x) := by
  constructor <;>
  · refine handled_vis _ state fun first next step => ?_
    obtain ⟨rfl, rfl⟩ := step
    refine handled_vis _ _ fun second _ step => ?_
    obtain ⟨rfl, _⟩ := step
    exact .refl _

/-- The trees differ when the same reply is given twice. -/
private theorem twice_ne_crossed (capture : Val Bit) (x : Val Packet) : twice capture x ≠ crossed capture x := by
  intro same
  have seen : HasTrace (twice capture x) (.exchange (.ask (bit capture) (tagOf x)) false
      (.exchange (.ask (bit capture) false) false (.result (capture, packet false)))) :=
    (hasTrace_vis_exchange_iff _ _ _ _).mpr ((hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _))
  rw [same] at seen
  have inner : HasTrace (vis (Event.ask (bit capture) false) fun _ => (ret (capture, packet (!false)) : Tree Event Packed))
      (.exchange (.ask (bit capture) false) false (.result (capture, packet false))) :=
    (hasTrace_vis_exchange_iff _ _ _ _).mp seen
  have returned : out (ret (capture, packet (!false)) : Tree Event Packed) =
      Part.some (.ret (capture, packet false)) := (hasTrace_vis_exchange_iff _ _ _ _).mp inner
  rw [out_ret] at returned
  have exits : packet (!false) = packet false := congrArg Prod.snd (Visible.ret.inj (Part.some_injective returned))
  exact Bool.noConfusion (packet_injective exits)

/-- The two composites are different native classes. -/
private theorem native_differ : term (Case.seq route route) ≠ term (Case.seq route echo) := by
  intro same
  have trees := run_pack_congr (M := instructions) (Quotient.exact same)
    ((.inl PUnit.unit, .inl PUnit.unit) : Packed)
  rw [run_twice, run_crossed] at trees
  exact twice_ne_crossed _ _ trees

private theorem policy_collapses (w : Packed) (state : Bool) :
    HandledTraceLE policy state ((pack captures (Case.seq route route)).run instructions w)
        ((pack captures (Case.seq route echo)).run instructions w) ∧
      HandledTraceLE policy state ((pack captures (Case.seq route echo)).run instructions w)
        ((pack captures (Case.seq route route)).run instructions w) := by
  have left : (pack captures (Case.seq route route)).run instructions w = twice w.1 w.2 := run_twice w.1 w.2
  have right : (pack captures (Case.seq route echo)).run instructions w = crossed w.1 w.2 := run_crossed w.1 w.2
  rw [left, right]
  exact twice_equiv_crossed state w.1 w.2

/-- The functor at this policy sends both classes to the same arrow. It is
not faithful. -/
example : term (Case.seq route route) ≠ term (Case.seq route echo) ∧
    semantics.map (term (Case.seq route route)) = semantics.map (term (Case.seq route echo)) := by
  exact ⟨native_differ, Quotient.sound
    ⟨fun w state => (policy_collapses w state).1, fun w state => (policy_collapses w state).2⟩⟩

/-! ## Written graphs through the actual emitter -/

private def written : Interface Op captures input := ⟨exits, nonempty⟩
private def graph (p : CheckedTable Op Source exits) : written ⟶ written := Quotient.mk _ p

/-- The checked graph read back from the captured term. -/
private def rebuilt : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty route.2

private abbrev ssaSemantics := ssaHandledFunctor instructions policy input

example : rebuilt.table.check = true := rfl

example : ssaSemantics.map (graph rebuilt) = HandledTrace.Arrow.ofProgram (pack captures rebuilt.toLetCase) :=
  ssaHandledFunctor_map_mk instructions policy input (X := written) (Y := written) rebuilt

/-- Both triangles over the emitter and the readback commute. -/
example : emitFunctor input ⋙ semantics = ssaSemantics := rfl
example : readbackFunctor input ⋙ ssaSemantics = semantics :=
  readbackFunctor_comp_ssaHandledFunctor instructions policy input

example : ssaSemantics.map (𝟙 written) = 𝟙 (ssaSemantics.obj written) := ssaSemantics.map_id written
example : ssaSemantics.map (graph rebuilt ≫ graph rebuilt) =
    ssaSemantics.map (graph rebuilt) ≫ ssaSemantics.map (graph rebuilt) :=
  ssaSemantics.map_comp (graph rebuilt) (graph rebuilt)

/-- The emitted graph has the same tree as the term it was read from. -/
private theorem run_rebuilt (w : Packed) :
    (pack captures rebuilt.toLetCase).run instructions w = stage w.1 w.2 :=
  (run_pack_congr (M := instructions) (CheckedTable.ofLetCase_emit false nonempty route.2) w).trans
    (run_route w.1 w.2)

/-- The emitted written link makes the two requests in order with the same
older capture, as an equality of trees. -/
private theorem run_linked (capture : Val Bit) (x : Val Packet) :
    (pack captures (seq rebuilt rebuilt).toLetCase).run instructions (capture, x) = twice capture x := by
  have stages : (pack captures rebuilt.toLetCase).run instructions = fun w => stage w.1 w.2 :=
    funext run_rebuilt
  rw [run_pack_congr (M := instructions) (emit_seq_equiv input rebuilt rebuilt), run_pack_seq, stages]
  simp only [stage, vis_bind]
  refine congrArg (vis (Event.ask (bit capture) (tagOf x))) (funext fun first => ?_)
  erw [pure_bind]
  rw [tagOf_packet]

/-- The written link shows the same state-dependent path as the native let. -/
example (state : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTrace policy state ((pack captures (seq rebuilt rebuilt).toLetCase).run instructions (capture, x))
      (.exchange (.ask (bit capture) (tagOf x)) state
        (.exchange (.ask (bit capture) state) (!state) (.result (capture, packet (!state))))) := by
  rw [run_linked]
  exact ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr ((hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _)),
    ⟨!state, ⟨rfl, rfl⟩, ⟨!!state, ⟨rfl, rfl⟩, trivial⟩⟩⟩

/-- The contextual equation for the emitted link, at every older environment. -/
example (ρ : BoundEnv Val captures) (x : Val Packet) :
    (seq rebuilt rebuilt).toLetCase.2.denote Val instructions (fun x => x.elim) (ρ.snoc x) =
      (rebuilt.toLetCase.2.denote Val instructions (fun x => x.elim) (ρ.snoc x) >>= fun y =>
        rebuilt.toLetCase.2.denote Val instructions (fun x => x.elim) (ρ.snoc y)) :=
  denote_emit_seq input rebuilt rebuilt ρ x

/-! ## No older captures -/

private theorem emptyInput : StructuralContext (.nil : Context 0) := .nil

private def closed : Operand Op (BoundCtx.nil.snoc Packet) Packet :=
  ⟨.case (.bv 0) (.inr (.inl .unit)) (.inl .unit), .case .bv (.inr (.inl .unit)) (.inl .unit)⟩

private def closedObject : Case.Interface Op .nil emptyInput := ⟨exits, nonempty⟩

/-- The packed program is the operand, and the object is the packed exit type. -/
example : pack .nil closed = closed := rfl
example : ((handledFunctor instructions policy emptyInput).obj closedObject).ty = Packet := rfl
example : (handledFunctor instructions policy emptyInput).map
    (X := closedObject) (Y := closedObject) (Quotient.mk _ closed) = HandledTrace.Arrow.ofProgram closed :=
  rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Tests
