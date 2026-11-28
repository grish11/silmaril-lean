module

import Silmaril.SSA.Isotope.LetCase.HandledTrace.Thms

section

namespace Silmaril.Isotope.LetCase.HandledTrace.Regression

open Silmaril.Elgot.ITree Silmaril.Isotope.Semantics
open Silmaril.Isotope.LetCase.LocallyNameless

private inductive Event : Type → Type where
  | advance : Event Unit
  | inspect : Event Unit

private def step : Handler Bool Event
  | ⟨_, .advance⟩, _, _, next => next = true
  | ⟨_, .inspect⟩, current, _, next => current = true ∧ next = current

private abbrev D := Ty.denote (fun _ : Empty => PUnit.{2})
private abbrev Γ₀ : Ctx Empty (Ty Empty) := .nil
private abbrev input : BoundCtx (Ty Empty) 1 := .snoc .nil .unit
private abbrev tagged : Ty Empty := .coprod .unit .unit

local instance : HasTy Bool (Ty Empty) := ⟨fun _ => .unit, fun _ => .unit⟩

private def instructions : InstructionModel D Bool (Tree Event) :=
  ⟨fun op _ => vis (if op then .inspect else .advance) (fun _ => ret PUnit.unit)⟩

private def advance : Derivation Bool Γ₀ .nil (.op false .unit) Ty.unit := .op .unit

private def inspectLeft : Derivation Bool Γ₀ input
    (.let₁ (.op true (.bv 0)) (.inl .unit)) tagged := .let₁ (.op .bv) (.inl .unit)

private def inspectRight : Derivation Bool Γ₀ input
    (.let₁ (.op true (.bv 0)) (.inr .unit)) tagged := .let₁ (.op .bv) (.inr .unit)

private abbrev run {n : Nat} {β : BoundCtx (Ty Empty) n} {t : Tm Empty Bool n} {A}
    (d : Derivation Bool Γ₀ β t A) (ρ : BoundEnv D β) : Tree Event (D A) :=
  d.denote D instructions (fun x => x.elim) ρ

private def ambient : BoundEnv D (.nil : BoundCtx (Ty Empty) 0) := fun i => i.elim0

private theorem leftTree :
    run inspectLeft (ambient.snoc PUnit.unit) = vis .inspect (fun _ => ret (.inl PUnit.unit)) := by
  change (((pure PUnit.unit : Tree Event PUnit.{2}) >>= fun _ =>
    vis Event.inspect (fun _ => (pure PUnit.unit : Tree Event PUnit.{2}))) >>= fun _ =>
      (pure PUnit.unit : Tree Event PUnit.{2}) >>= fun _ =>
        pure (Sum.inl PUnit.unit : PUnit.{2} ⊕ PUnit.{2})) = _
  simp only [pure_bind, vis_bind]
  rfl

private theorem rightTree :
    run inspectRight (ambient.snoc PUnit.unit) = vis .inspect (fun _ => ret (.inr PUnit.unit)) := by
  change (((pure PUnit.unit : Tree Event PUnit.{2}) >>= fun _ =>
    vis Event.inspect (fun _ => (pure PUnit.unit : Tree Event PUnit.{2}))) >>= fun _ =>
      (pure PUnit.unit : Tree Event PUnit.{2}) >>= fun _ =>
        pure (Sum.inr PUnit.unit : PUnit.{2} ⊕ PUnit.{2})) = _
  simp only [pure_bind, vis_bind]
  rfl

-- Both continuations expose a pending inspect even when its reply is denied.
private theorem initialOnly :
    HandledTraceLE step false (run inspectLeft (ambient.snoc PUnit.unit))
      (run inspectRight (ambient.snoc PUnit.unit)) := by
  rw [leftTree, rightTree]
  intro trace seen
  cases trace with
  | «prefix» => exact seen
  | request event =>
    exact ⟨(hasTrace_vis_request_iff _ _ event).mpr ((hasTrace_vis_request_iff _ _ event).mp seen.1), seen.2⟩
  | exchange event reply tail =>
    obtain ⟨sameType, sameEvent, _⟩ := (hasTrace_vis_exchange _ _ event reply tail).mp seen.1
    cases sameType
    cases sameEvent
    obtain ⟨_, allowed, _⟩ := seen.2
    exact Bool.noConfusion allowed.1
  | result _ =>
    have impossible := seen.1
    simp [HasTrace, out_vis] at impossible

private theorem advanceTree :
    run advance ambient = vis .advance (fun _ => ret PUnit.unit) := by
  change ((pure PUnit.unit : Tree Event PUnit.{2}) >>= fun _ => instructions.eval false PUnit.unit) = _
  rw [pure_bind]
  rfl

private def witness : Trace Event (D tagged) :=
  .exchange .advance () (.exchange .inspect () (.result (.inl PUnit.unit)))

-- The same initial state cannot be used to check the continuations: advance
-- enables inspect, and the typed returns at its two positions differ.
private theorem sequencedFailure :
    ¬ HandledTraceLE step false (run (.let₁ advance inspectLeft) ambient)
      (run (.let₁ advance inspectRight) ambient) := by
  intro includes
  have sequence {t : Tm Empty Bool 1} (d : Derivation Bool Γ₀ input t tagged) :
      run (.let₁ advance d) ambient =
        vis .advance (fun _ => run d (ambient.snoc PUnit.unit)) := by
    change ((run advance ambient : Tree Event PUnit.{2}) >>= fun a => run d (ambient.snoc a)) = _
    rw [advanceTree]
    change (vis Event.advance (fun _ => (pure PUnit.unit : Tree Event PUnit.{2})) >>= fun a =>
      run d (ambient.snoc a)) = _
    simp only [vis_bind, pure_bind]
  rw [sequence, sequence, leftTree, rightTree] at includes
  have seen : HasTrace (vis .advance (fun _ => vis .inspect (fun _ => ret (.inl PUnit.unit)))) witness :=
    (hasTrace_vis_exchange_iff _ _ _ _).mpr ((hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _))
  have replay : Replay step false witness := ⟨true, rfl, true, ⟨rfl, rfl⟩, trivial⟩
  have absent := (includes witness ⟨seen, replay⟩).1
  simp only [witness, hasTrace_vis_exchange_iff] at absent
  have distinct : (Sum.inr PUnit.unit : PUnit.{2} ⊕ PUnit.{2}) = Sum.inl PUnit.unit :=
    ret_inj.mp (out_injective (E := Event) (absent.trans (out_ret _).symm))
  cases distinct

example :
    HandledTraceLE step false (run inspectLeft (ambient.snoc PUnit.unit))
      (run inspectRight (ambient.snoc PUnit.unit)) ∧
      ¬ HandledTraceLE step false (run (.let₁ advance inspectLeft) ambient)
        (run (.let₁ advance inspectRight) ambient) :=
  ⟨initialOnly, sequencedFailure⟩

private def advanceViaLet :
    Derivation Bool Γ₀ .nil (.let₁ (.op false .unit) (.bv 0)) Ty.unit := .let₁ advance .bv

-- The two producers differ by an administrative let, while the native
-- continuation sees the same reply, ordered result type, and replay state.
example : HandledTraceLE step false (run (.let₁ advance inspectLeft) ambient)
    (run (.let₁ advanceViaLet inspectLeft) ambient) := by
  apply Derivation.handledTraceLE_let₁
  · change HandledTraceLE step false (run advance ambient)
      (run advance ambient >>= (pure : PUnit.{2} → Tree Event PUnit.{2}))
    erw [bind_pure]
  · intro y value _
    exact .refl _

-- The first component models an ordered result; the second is a live register.
-- Forgetting it makes the results equal, but a common store reader separates them.
private def first : Tree Event (Unit × Bool) := pure ((), false)
private def second : Tree Event (Unit × Bool) := pure ((), true)

example :
    HandledTraceLE step false (first >>= fun p => pure p.1) (second >>= fun p => pure p.1) ∧
    ¬ HandledTraceLE step false (first >>= fun p => pure p.2) (second >>= fun p => pure p.2) := by
  constructor
  · simpa only [first, second, pure_bind] using
      (HandledTraceLE.refl (step := step) (x := false) (pure () : Tree Event Unit))
  · intro includes
    have observed := includes (.result false) ⟨by rw [first, pure_bind]; exact out_ret _, trivial⟩
    rw [second, pure_bind] at observed
    exact Bool.noConfusion (ret_inj.mp (out_injective (observed.1.trans (out_ret _).symm)))

end Silmaril.Isotope.LetCase.HandledTrace.Regression

end
