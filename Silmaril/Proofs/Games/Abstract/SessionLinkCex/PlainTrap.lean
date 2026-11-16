module

public import Silmaril.Games.Abstract.SessionLinkCex.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DivComp.Defs

/-!
# Linking counterexamples: a plain server trap

The client calls the plainly trapping server once and returns. The composite answers the client's
question; the linked triple serves a call only by a returning round of the server, so it never
returns.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionLinkCex

variable {E : Sig.{0}}

theorem trapServer_rounds {s s₁ : Unit} {rs : List (Unit × List (Call E) × (Unit ⊕ Unit))}
    (h : Rounds (trapServer (E := E)) s rs s₁) : rs = [] := by
  cases h with
  | nil => rfl
  | cons h _ => simp [trapServer] at h

theorem not_linkS_ret {σ : Unit × Unit} {c : List (Call E)} {y : Unit ⊕ Unit} {σ₁ : Unit × Unit} :
    (c, End.ret y σ₁) ∉ (linkS (trapServer (E := E)) trapClient).1 σ () := by
  rintro (⟨rs, s₁, e, hr, he, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩)
  · cases trapServer_rounds hr
    simp [trapClient, served] at he
  · simp at hx
  · simp at hx

theorem storeDet_linkS_trap : StoreDet (linkS (trapServer (E := E)) trapClient) :=
  fun _ _ _ _ _ _ h _ => absurd h not_linkS_ret

theorem det_trapServer : AFun.Det (trapServer (E := E)).1 := by
  rintro _ _ x y hx hy
  simp only [trapServer, Set.mem_singleton_iff] at hx hy
  subst hx hy
  rfl

theorem det_trapClient : AFun.Det trapClient.1 := by
  rintro _ _ x y hx hy
  simp only [trapClient, Set.mem_singleton_iff] at hx hy
  subst hx hy
  exact ⟨rfl, fun _ => rfl⟩

theorem not_noPlainTrap_trapServer : ¬ NoPlainTrap (trapServer (E := E)) :=
  fun h => h () () [] rfl

theorem askRet_mem_comp :
    [.inr (.ask ()), .inr (.ans () (Sum.inl ()))] ∈ ((threadS (trapServer (E := E)) ()).comp (threadS trapClient ())).toStrategy := by
  have hs : ([.inr (.ask ()), .inr (.ans () (Sum.inr ()))] : List (Move E (sig1 Unit Unit))) ∈
      (threadS (trapServer (E := E)) ()).toStrategy :=
    mem_srounds (rs := [((), [], .inr ())]) |>.2 (.inr ⟨[], (), [], rfl, (), .nil _, rfl⟩)
  have ht : ([.inr (.ask ()), .inl (.ask ()), .inl (.ans () (Sum.inr ())),
      .inr (.ans () (Sum.inl ()))] : List (Move (sig1 Unit Unit) (sig1 Unit Unit))) ∈
      (threadS trapClient ()).toStrategy :=
    mem_srounds (rs := [((), [(⟨(), Sum.inr ()⟩ : Call (sig1 Unit Unit))], .inl ())]) |>.2
      (.inl ⟨(), .cons (s₁ := ()) rfl (.nil _)⟩)
  exact ⟨_, hs, _, ht, .right _ (.sync _ (.sync _ (.right _ .nil)))⟩

theorem askRet_not_mem_linkS :
    [.inr (.ask ()), .inr (.ans () (Sum.inl ()))] ∉ (threadS (linkS (trapServer (E := E)) trapClient) ((), ())).toStrategy := by
  intro h
  have h' : sroundsMoves [((), ([] : List (Call E)), (.inl () : Unit ⊕ Unit))] ∈
      (threadS (linkS (trapServer (E := E)) trapClient) ((), ())).toStrategy := h
  rcases mem_srounds.1 h' with ⟨_, hr⟩ | ⟨rs', _, _, he, _⟩
  · cases hr with
    | cons hr _ => exact not_linkS_ret hr
  · rcases rs' with _ | ⟨_, _ | _⟩ <;> simp at he

end Silmaril.Proofs.Games.Abstract.SessionLinkCex
