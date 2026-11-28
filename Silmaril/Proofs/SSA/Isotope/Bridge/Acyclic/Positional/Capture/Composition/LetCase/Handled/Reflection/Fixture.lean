module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Thms

/-! # One older capture, two unit exits, and two composites

The shared fixture of the free-interpretation regressions. -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Isotope.Semantics (BoundEnv)
open LetCase.Structural.Finite (Context Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.toSmall Structured.Event)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

inductive Op | ask

abbrev bitShape : Shape := .sum .unit .unit
abbrev Bit := bitShape.ty
abbrev captures : Context 1 := .snoc .nil Bit
abbrev exits : LCtx Types := [.unit, .unit]
abbrev Packet := packedExitType exits
abbrev Source := captures.snoc Packet

instance : LetCase.Structural.Finite.Signature Op where
  source _ := .pair bitShape bitShape
  target _ := bitShape

theorem input : StructuralContext captures := .snoc .nil bitShape
theorem nonempty : exits ≠ [] := List.cons_ne_nil _ _

local notation "Value" => LetCase.Structural.Finite.Value
local notation "small" => Structured.toSmall Atoms

/-- Ask with the older capture and the input tag, then leave by the exit
named by the reply. Both exits carry a unit payload. -/
def route : Operand Op Source Packet :=
  ⟨.let₁ (.op .ask (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inl .bv) (.inr (.inl .bv)))⟩

/-- Ask with the older capture and the input tag, ignore the reply, and
leave by the exit opposite to the input tag. -/
def echo : Operand Op Source Packet :=
  ⟨.let₁ (.op .ask (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 1) (.inr (.inl .unit)) (.inl .unit)),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inr (.inl .unit)) (.inl .unit))⟩

abbrev Packed := Val (wrap captures Packet)

def tagOf : Val Packet → Val Bit
  | .inl _ => .inl PUnit.unit
  | .inr _ => .inr PUnit.unit

def packet : Value Bit → Val Packet
  | .inl _ => .inl PUnit.unit
  | .inr _ => .inr (.inl PUnit.unit)

def other : Val Packet → Val Packet
  | .inl _ => .inr (.inl PUnit.unit)
  | .inr _ => .inl PUnit.unit

/-- The request names the older capture and the input tag. -/
def request (capture tag : Val Bit) : Value (instrSrc Op.ask) :=
  small (instrSrc Op.ask) (capture, tag)

def stage (capture : Val Bit) (x : Val Packet) : Tree (Events Op) Packed :=
  vis (.call Op.ask (request capture (tagOf x))) (fun reply => ret (capture, packet reply))

theorem leave_low (capture : Val Bit) {t : Tree (Events Op) (Val Packet)}
    (computed : t = ((pure PUnit.unit : Tree (Events Op) (Val Ty.unit)) >>= fun a =>
      (pure (Sum.inl a) : Tree (Events Op) (Val Packet)))) :
    (t >>= fun y => (pure (capture, y) : Tree (Events Op) Packed)) = ret (capture, .inl PUnit.unit) := by
  subst computed
  simp only [pure_bind]
  rfl

theorem leave_high (capture : Val Bit) {t : Tree (Events Op) (Val Packet)}
    (computed : t = (((pure PUnit.unit : Tree (Events Op) (Val Ty.unit)) >>= fun a =>
      (pure (Sum.inl a) : Tree (Events Op) (Val (packedExitType [Ty.unit])))) >>= fun b =>
      (pure (Sum.inr b) : Tree (Events Op) (Val Packet)))) :
    (t >>= fun y => (pure (capture, y) : Tree (Events Op) Packed)) = ret (capture, .inr (.inl PUnit.unit)) := by
  subst computed
  simp only [pure_bind]
  rfl

/-- The packed term makes one free request naming the older capture and
the input tag, and returns the capture beside the exit named by the reply. -/
theorem run_route (capture : Val Bit) (x : Val Packet) :
    (pack captures route).run (model Op) (capture, x) = stage capture x := by
  refine (run_pack (M := model Op) captures route
    (BoundEnv.snoc (β := .nil) (fun i => i.elim0) capture) x).trans ?_
  simp only [route, Derivation.denote]
  cases x with
  | inl u =>
    erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    erw [bind_assoc, model_eval_bind]
    refine congrArg (vis (Structured.Event.call Op.ask (request capture (tagOf (.inl u))))) (funext fun reply => ?_)
    cases reply <;> erw [pure_bind]
    · exact leave_low capture rfl
    · exact leave_high capture rfl
  | inr u =>
    erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    erw [bind_assoc, pure_bind, model_eval_bind]
    refine congrArg (vis (Structured.Event.call Op.ask (request capture (tagOf (.inr u))))) (funext fun reply => ?_)
    cases reply <;> erw [pure_bind]
    · exact leave_low capture rfl
    · exact leave_high capture rfl

theorem run_echo (capture : Val Bit) (x : Val Packet) :
    (pack captures echo).run (model Op) (capture, x) =
      vis (.call Op.ask (request capture (tagOf x))) (fun _ => ret (capture, other x)) := by
  refine (run_pack (M := model Op) captures echo
    (BoundEnv.snoc (β := .nil) (fun i => i.elim0) capture) x).trans ?_
  simp only [echo, Derivation.denote]
  cases x with
  | inl u =>
    erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    erw [bind_assoc, model_eval_bind]
    refine congrArg (vis (Structured.Event.call Op.ask (request capture (tagOf (.inl u))))) (funext fun reply => ?_)
    erw [pure_bind]
    exact leave_high capture rfl
  | inr u =>
    erw [pure_bind, pure_bind, pure_bind, pure_bind, pure_bind]
    erw [bind_assoc, pure_bind, model_eval_bind]
    refine congrArg (vis (Structured.Event.call Op.ask (request capture (tagOf (.inr u))))) (funext fun reply => ?_)
    erw [pure_bind]
    exact leave_low capture rfl

/-- Two stages: the second request repeats the capture and names the exit
taken by the first stage. -/
def twice (capture : Val Bit) (x : Val Packet) : Tree (Events Op) Packed :=
  vis (.call Op.ask (request capture (tagOf x))) fun first =>
    vis (.call Op.ask (request capture (tagOf (packet first)))) fun second => ret (capture, packet second)

/-- Two requests, leaving by the exit opposite to the first reply. -/
def crossed (capture : Val Bit) (x : Val Packet) : Tree (Events Op) Packed :=
  vis (.call Op.ask (request capture (tagOf x))) fun first =>
    vis (.call Op.ask (request capture (tagOf (packet first)))) fun _ => ret (capture, other (packet first))

theorem run_twice (w : Packed) :
    (pack captures (Case.seq route route)).run (model Op) w = twice w.1 w.2 := by
  have stages : (pack captures route).run (model Op) = fun w => stage w.1 w.2 :=
    funext fun w => run_route w.1 w.2
  rw [run_pack_seq, stages]
  simp only [stage, vis_bind]
  refine congrArg (vis (Structured.Event.call Op.ask (request w.1 (tagOf w.2)))) (funext fun first => ?_)
  erw [pure_bind]

theorem run_crossed (w : Packed) :
    (pack captures (Case.seq route echo)).run (model Op) w = crossed w.1 w.2 := by
  have second : (pack captures echo).run (model Op) = fun w =>
      vis (.call Op.ask (request w.1 (tagOf w.2))) (fun _ => ret (w.1, other w.2)) :=
    funext fun w => run_echo w.1 w.2
  have first : (pack captures route).run (model Op) = fun w => stage w.1 w.2 :=
    funext fun w => run_route w.1 w.2
  rw [run_pack_seq, first, second]
  simp only [stage, vis_bind]
  refine congrArg (vis (Structured.Event.call Op.ask (request w.1 (tagOf w.2)))) (funext fun first => ?_)
  erw [pure_bind]

/-! ## The two arrows -/

def native : Case.Interface Op captures input := ⟨exits, nonempty⟩
def term (a : Operand Op Source Packet) : native ⟶ native := Quotient.mk _ a

abbrev both : native ⟶ native := term (Case.seq route route)
abbrev mixed : native ⟶ native := term (Case.seq route echo)

/-! ## A separating history

The same reply is given twice. The first composite then leaves by the exit
named by that reply and the second leaves by the opposite exit. -/

abbrev low : Value Bit := .inl PUnit.unit
abbrev start : Packed := (.inl PUnit.unit, .inl PUnit.unit)

def repeated : Log Empty Op :=
  FreeMonoid.of ⟨Op.ask, request start.1 (tagOf start.2), low⟩ *
    (FreeMonoid.of ⟨Op.ask, request start.1 (tagOf (packet low)), low⟩ * 1)

abbrev finish : Packed := (start.1, packet low)

theorem twice_shows : HasTrace (twice start.1 start.2) (history repeated finish) := by
  simp only [twice, repeated, history_cons, history_one, hasTrace_vis_exchange_iff]
  exact out_ret _

theorem crossed_hides : ¬ HasTrace (crossed start.1 start.2) (history repeated finish) := by
  simp only [crossed, repeated, history_cons, history_one, hasTrace_vis_exchange_iff]
  intro returned
  have same : out (ret ((start.1, other (packet low)) : Packed) : Tree (Events Op) Packed) =
      Part.some (.ret finish) := returned
  rw [out_ret] at same
  have exits : other (packet low) = packet low := congrArg Prod.snd (Visible.ret.inj (Part.some_injective same))
  cases exits

/-- The two arrows are different native classes. -/
theorem native_differ : both ≠ mixed := by
  intro same
  have trees := run_pack_eq_of_equiv (Quotient.exact same) start
  rw [run_twice, run_crossed] at trees
  exact crossed_hides (trees ▸ twice_shows)

/-! ## The state-flipping policy

The reply is the current state and each exchange flips the state. -/

def replyBit : (f : Op) → Value (instrTrg f) → Bool
  | .ask, .inl _ => false
  | .ask, .inr _ => true

def alternating : Handler Bool (Events Op)
  | ⟨_, .call f _⟩, state, reply, next => replyBit f reply = state ∧ next = !state

theorem alternating_vis {R : Type} (e : Events Op R) {k l : R → Tree (Events Op) Packed} (state : Bool)
    (admitted : ∀ reply next, alternating ⟨R, e⟩ state reply next →
      HandledTraceLE alternating next (k reply) (l reply)) :
    HandledTraceLE alternating state (vis e k) (vis e l) := by
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

theorem opposite {first second : Value Bit} {state : Bool}
    (one : replyBit Op.ask first = state) (two : replyBit Op.ask second = !state) :
    packet second = other (packet first) := by
  subst one
  rcases first with _ | _ <;> rcases second with _ | _ <;> first | rfl | cases two

theorem alternating_collapses (state : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTraceLE alternating state (twice capture x) (crossed capture x) ∧
      HandledTraceLE alternating state (crossed capture x) (twice capture x) := by
  constructor <;>
  · refine alternating_vis _ state fun first next step => ?_
    obtain ⟨one, rfl⟩ := step
    refine alternating_vis _ _ fun second _ step => ?_
    rw [opposite one step.1]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
