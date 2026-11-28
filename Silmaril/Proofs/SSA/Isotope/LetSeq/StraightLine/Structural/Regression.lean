module

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Thms
import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Thms

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Semantics.NondeterministicTrace
open scoped Structural

set_option backward.isDefEq.respectTransparency false

private inductive Generator where
  | send
  | receive

private instance : Signature Bool Generator where
  argument
    | .send => .pair (.atom false) .unit
    | .receive => .pair .unit (.atom true)
  reply
    | .send => .unit
    | .receive => .pair (.atom false) (.pair .unit (.atom true))

private abbrev inputShape : Shape Bool := Shape.pack [.atom false, .atom true]
private abbrev Result : Ty Bool := .product (.base false) (.product .unit (.base true))

private def both : Term Generator 1 :=
  .let₂ (.bv 0) (.let₂ (.bv 0)
    (.let₁ (.op .send (.pair (.bv 3) .unit)) (.op .receive (.pair .unit (.bv 2)))))

private def receiveOnly : Term Generator 1 :=
  .let₂ (.bv 0) (.let₂ (.bv 0) (.op .receive (.pair .unit (.bv 1))))

private def bothTyped : Derivation Generator Γ₀ (Packed inputShape) both Result :=
  .let₂ .bv (.let₂ .bv (.let₁ (.op (.pair .bv .unit)) (.op (.pair .unit .bv))))

private def receiveTyped : Derivation Generator Γ₀ (Packed inputShape) receiveOnly Result :=
  .let₂ .bv (.let₂ .bv (.op (.pair .unit .bv)))

-- Only the native typing is supplied. The first operation's reply has no
-- atom leaves, and the second operation's argument and reply have distinct shapes.
example : ∃ u : Term Generator (packedUnpack inputShape).size,
    ∃ _ : Normal (packedUnpack inputShape).context u Result,
      Equiv false Γ₀ (Packed inputShape) both ((packedUnpack inputShape).split.wrap u) Result :=
  normalize_packed bothTyped

private def result : Value Result := ((2 : Nat), ((), (3 : Nat)))
private def sent : Event (α := Bool) (Φ := Generator) :=
  ⟨.send, ((0 : Nat), ()), ()⟩
private def received : Event (α := Bool) (Φ := Generator) :=
  ⟨.receive, ((), (1 : Nat)), result⟩
private def observed : Log Bool Generator := FreeMonoid.of sent * FreeMonoid.of received

private theorem both_observed :
    (result, observed) ∈ (run bothTyped (packedEnv inputShape (inputShape.fresh 0))).outcomes := by
  simp only [bothTyped, run, Derivation.denote, pure_bind]
  apply mem_request_trace.mpr
  exact ⟨⟨⟩, FreeMonoid.of received, ⟨result, rfl⟩, rfl⟩

-- Ignoring the unit result does not erase the first event.
private theorem both_ne_receive : ¬ Equiv false Γ₀ (Packed inputShape) both receiveOnly Result := by
  intro eq
  have equal := (packed_run_eq_iff_native bothTyped receiveTyped).mpr eq
  have trace := both_observed
  rw [equal] at trace
  simp only [receiveTyped, run, Derivation.denote, pure_bind] at trace
  obtain ⟨reply, observation⟩ := trace
  have log := congrArg Prod.snd observation
  have words := congrArg FreeMonoid.toList log
  have different : Generator.receive = Generator.send :=
    congrArg Event.generator (List.cons.inj words).1
  cases different

-- The same typed trace is observed by the categorical arrow.
example : (result, observed) ∈
    ((Categorical.traceArrow bothTyped).of ((), ((), inputShape.fresh 0))).outcomes := by
  rw [Categorical.traceArrow_apply_packed]
  exact both_observed

example : ¬ Categorical.Valid bothTyped receiveTyped :=
  fun h => both_ne_receive ((Categorical.equiv_iff_valid bothTyped receiveTyped).mpr h)

end Silmaril.Isotope.LetSeq.StraightLine.Structural
