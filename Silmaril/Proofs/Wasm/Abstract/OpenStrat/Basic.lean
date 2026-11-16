module

public import Silmaril.Wasm.Abstract.OpenStrat.Defs
public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms
public import Silmaril.Games.Abstract.StratHost.Defs

/-!
# The open, host-independent native strategy of invocations (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.OpenStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratHost
  Silmaril.Wasm.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem mem_funDXP_iff {s : Store H} {a : Nat} {vs : List Val}
    {x : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} :
    x ∈ wasmEvFunDXP s (a, vs) ↔
      x ∈ wasmEvFunXP s (a, vs) ∨ (x.2 = .div ∧ x ∈ wasmEvFunDXP s (a, vs)) := by
  by_cases hx : x.2 = .div
  · exact ⟨fun h => .inr ⟨hx, h⟩, fun h => h.elim (fun h => Or.inl (Or.inl h)) And.right⟩
  · rw [wasmEvFunDXP_of_ne_div hx]
    exact ⟨.inl, fun h => h.elim id fun h => absurd h.1 hx⟩

theorem mem_funD_iff {s : Store H} {a : Nat} {vs : List Val}
    {x : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} :
    x ∈ wasmEvFunD s (a, vs) ↔
      x ∈ wasmEvFun s (a, vs) ∨ (x.2 = .div ∧ x ∈ wasmEvFunD s (a, vs)) := by
  by_cases hx : x.2 = .div
  · exact ⟨fun h => .inr ⟨hx, h⟩, fun h => h.elim (fun h => Or.inl (Or.inl h)) And.right⟩
  · rw [wasmEvFunD_of_ne_div hx]
    exact ⟨.inl, fun h => h.elim id fun h => absurd h.1 hx⟩

theorem obsTriple_natXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    obsTriple Ok (fun s q => NatObsXP host s q.1 q.2) =
      hostRestrict (coreHostRel host) (guardT Ok openTripleXP) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext s ⟨a, vs⟩ <;> ext x
  · obtain ⟨cs, e⟩ := x
    show Ok s (a, vs) ∧ (((cs, e) ∈ wasmEvFunXP s (a, vs) ∧ _) ∨
      (e = .div ∧ (cs, End.div) ∈ wasmEvFunDXP s (a, vs) ∧ _)) ↔
      (Ok s (a, vs) ∧ (cs, e) ∈ wasmEvFunDXP s (a, vs)) ∧ _
    constructor
    · rintro ⟨hOk, ⟨h, hc⟩ | ⟨rfl, h, hc⟩⟩
      · exact ⟨⟨hOk, mem_funDXP_iff.2 (.inl h)⟩, hc⟩
      · exact ⟨⟨hOk, h⟩, hc⟩
    · rintro ⟨⟨hOk, h⟩, hc⟩
      rcases mem_funDXP_iff.1 h with h | ⟨he, h⟩
      · exact ⟨hOk, .inl ⟨h, hc⟩⟩
      · obtain rfl : e = .div := he
        exact ⟨hOk, .inr ⟨rfl, h, hc⟩⟩
  · show Ok s (a, vs) ∧ ((x ∈ wasmEvPendXP s (a, vs) ∧ _ ∧ _) ∨
      (x ∈ wasmEvPendXP s (a, vs) ∧ _ ∧ _)) ↔
      (Ok s (a, vs) ∧ x ∈ wasmEvPendXP s (a, vs)) ∧ _ ∧ _
    constructor
    · rintro ⟨hOk, ⟨h, hc, hb⟩ | ⟨h, hc, hd⟩⟩
      · exact ⟨⟨hOk, h⟩, hc, .inl hb⟩
      · exact ⟨⟨hOk, h⟩, hc, .inr hd⟩
    · rintro ⟨⟨hOk, h⟩, hc, hb | hd⟩
      · exact ⟨hOk, .inl ⟨h, hc, hb⟩⟩
      · exact ⟨hOk, .inr ⟨h, hc, hd⟩⟩
  · exact ⟨fun ⟨hOk, h, hc⟩ => ⟨⟨hOk, h⟩, hc⟩,
      fun ⟨⟨hOk, h⟩, hc⟩ => ⟨hOk, h, hc⟩⟩

theorem obsTriple_nat (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    obsTriple Ok (fun s q => NatObs host s q.1 q.2) =
      hostRestrict (coreHostRel host) (guardT Ok openTriple) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext s ⟨a, vs⟩ <;> ext x
  · obtain ⟨cs, e⟩ := x
    show Ok s (a, vs) ∧ (((cs, e) ∈ wasmEvFun s (a, vs) ∧ _) ∨
      (e = .div ∧ (cs, End.div) ∈ wasmEvFunD s (a, vs) ∧ _)) ↔
      (Ok s (a, vs) ∧ (cs, e) ∈ wasmEvFunD s (a, vs)) ∧ _
    constructor
    · rintro ⟨hOk, ⟨h, hc⟩ | ⟨rfl, h, hc⟩⟩
      · exact ⟨⟨hOk, mem_funD_iff.2 (.inl h)⟩, hc⟩
      · exact ⟨⟨hOk, h⟩, hc⟩
    · rintro ⟨⟨hOk, h⟩, hc⟩
      rcases mem_funD_iff.1 h with h | ⟨he, h⟩
      · exact ⟨hOk, .inl ⟨h, hc⟩⟩
      · obtain rfl : e = .div := he
        exact ⟨hOk, .inr ⟨rfl, h, hc⟩⟩
  · show Ok s (a, vs) ∧ ((x ∈ wasmEvPend s (a, vs) ∧ _ ∧ _) ∨
      (x ∈ wasmEvPend s (a, vs) ∧ _ ∧ _)) ↔
      (Ok s (a, vs) ∧ x ∈ wasmEvPend s (a, vs)) ∧ _ ∧ _
    constructor
    · rintro ⟨hOk, ⟨h, hc, hb⟩ | ⟨h, hc, hd⟩⟩
      · exact ⟨⟨hOk, h⟩, hc, .inl hb⟩
      · exact ⟨⟨hOk, h⟩, hc, .inr hd⟩
    · rintro ⟨⟨hOk, h⟩, hc, hb | hd⟩
      · exact ⟨hOk, .inl ⟨h, hc, hb⟩⟩
      · exact ⟨hOk, .inr ⟨h, hc, hd⟩⟩
  · exact ⟨fun ⟨hOk, h, hc⟩ => ⟨⟨hOk, h⟩, hc⟩,
      fun ⟨⟨hOk, h⟩, hc⟩ => ⟨hOk, h, hc⟩⟩

end Silmaril.Proofs.Wasm.Abstract.OpenStrat
