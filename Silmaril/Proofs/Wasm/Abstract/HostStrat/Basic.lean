module

public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Games.Abstract.StratObs.Thms

/-!
# Invocations against a host as canonical strategies (proofs)

`obsTriple_congr`: observation families that agree on the questions `Ok` give the same triple.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem obsTriple_congr {Ok : Store H → Nat × List Val → Prop}
    {O O' : Store H → Nat × List Val → FullObs H → Prop}
    (h : ∀ s q, Ok s q → ∀ x, O s q x ↔ O' s q x) : obsTriple Ok O = obsTriple Ok O' := by
  refine Prod.ext (funext fun s => funext fun q => Set.ext fun x => ?_)
    (Prod.ext (funext fun s => funext fun q => Set.ext fun x => ?_)
      (funext fun s => funext fun q => Set.ext fun x => ?_)) <;>
  simp only [obsTriple, Set.mem_ofPred_eq] <;>
  exact ⟨fun ⟨hq, hx⟩ => ⟨hq, by simpa only [h s q hq] using hx⟩,
    fun ⟨hq, hx⟩ => ⟨hq, by simpa only [h s q hq] using hx⟩⟩

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

theorem coreStratAt_mem_ret (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (ws : List Val) :
    (.inr (.ask ((), vs)) :: (StratObs.callMoves cs ++ [.inr (.ans ((), vs) (.inl (.inl ws, ())))]) :
        List (Move (wasmHostSig H) (funSig Unit (List Val) (List Val ⊕ Nat)))) ∈
        (coreStratAt P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ := by
  refine (StratObs.mem_ret () vs cs _ ()).trans ?_
  constructor
  · rintro ⟨⟨c, e⟩, ⟨hq, h⟩, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rcases h with h | ⟨rfl, _⟩
    · cases e with
      | ret b s₂ =>
        cases b with
        | inl ws' => cases he; exact ⟨hq, s₂, h⟩
        | inr _ => cases he
      | trap => cases he
      | div => cases he
    · cases he
  · rintro ⟨hq, s₂, h⟩
    exact ⟨(cs, .ret (.inl ws) s₂), ⟨hq, .inl h⟩, rfl⟩

theorem coreStratAt_mem_trap (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask ((), vs)) :: (StratObs.callMoves cs ++ [.inr (.ans ((), vs) (.inr PUnit.unit))]) :
        List (Move (wasmHostSig H) (funSig Unit (List Val) (List Val ⊕ Nat)))) ∈
        (coreStratAt P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  refine (StratObs.mem_trap () vs cs).trans ?_
  constructor
  · rintro ⟨⟨c, e⟩, ⟨hq, h⟩, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rcases h with h | ⟨rfl, _⟩
    · cases e with
      | ret b s₂ => cases he
      | trap => exact ⟨hq, h⟩
      | div => cases he
    · cases he
  · rintro ⟨hq, h⟩
    exact ⟨(cs, .trap), ⟨hq, .inl h⟩, rfl⟩

end Silmaril.Proofs.Wasm.Abstract.HostStrat
