module

public import Silmaril.Wasi.Component.Accept.Ref.HostSession.Defs
public import Silmaril.Wasi.Component.Accept.Ref.Bridge.Thms
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Thms

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.HostSession.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSession

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasi.Accept Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-! ## Bytes of argument lists -/

/-- **REF and the IR read the bytes of an argument list the same way**: `bytesOf?` of the
reference images is `args1 bytes?` of the IR values (P2 on one argument; both readings reject
other arities). -/
theorem bytesOf?_map_toRefVal : ∀ ws : List IVal, bytesOf? (ws.map toRefVal) = args1 bytes? ws
  | [] => rfl
  | [v] => by simpa [args1] using bytesOf?_toRefVal v
  | x :: y :: t => by
    simp only [List.map_cons, args1]
    generalize toRefVal x = a
    cases a <;> rfl

/-! ## The host log -/

variable {σ : Type} {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-- The log entry of an answered component import call. -/
def logEntry {n : Nat} (k : Fin n) (ws us : List IVal) : HLinked2.HostEvent :=
  (⟨k.val⟩, ws.map toRefVal, us.map toRefVal)

/-- **Every entry of the final log was in the initial log or is the entry of an answered call.** -/
theorem log_sub {n : Nat} :
    ∀ {ds : List (Σ _ : (sigN n).Op, Option Payload)} {s : σ} {L : List HLinked2.HostEvent}
      {st' : σ × List HLinked2.HostEvent}, HostRun (HLinked2.logG g) (s, L) ds st' →
      ∀ ev ∈ st'.2, ev ∈ L ∨ ∃ d ∈ ds, ∃ (k : Fin n) (ws us : List IVal),
        d = ⟨(k, .vals ws), some (.vals us)⟩ ∧ ev = logEntry k ws us
  | [], _, _, _, h => by
    cases h
    exact fun ev hev => .inl hev
  | ⟨q, R⟩ :: ds, s, L, st', h => by
    intro ev hev
    cases h with
    | cons hd hr =>
      rename_i s₁
      obtain ⟨k, ws, hq, hR⟩ := hd
      subst hq
      cases R with
      | none =>
        obtain ⟨-, rfl⟩ := hR
        rcases log_sub hr ev hev with h₁ | ⟨d, hd, h₂⟩
        · exact .inl h₁
        · exact .inr ⟨d, List.mem_cons_of_mem _ hd, h₂⟩
      | some p =>
        cases p with
        | flat _ => exact hR.elim
        | vals us =>
          obtain ⟨r, hg, hr'⟩ := Option.map_eq_some_iff.mp hR
          obtain ⟨s₂, L₂⟩ := s₁
          simp only [Prod.mk.injEq] at hr'
          obtain ⟨hr₁, rfl, rfl⟩ := hr'
          rcases log_sub hr ev hev with h₁ | ⟨d, hd, h₂⟩
          · rcases List.mem_append.mp h₁ with h₁ | h₁
            · exact .inl h₁
            · refine .inr ⟨_, List.mem_cons_self, k, ws, us, rfl, ?_⟩
              simpa [logEntry, hr₁] using h₁
          · exact .inr ⟨d, List.mem_cons_of_mem _ hd, h₂⟩

/-- **The log only grows, and records every answered call.** -/
theorem log_sup {n : Nat} :
    ∀ {ds : List (Σ _ : (sigN n).Op, Option Payload)} {s : σ} {L : List HLinked2.HostEvent}
      {st' : σ × List HLinked2.HostEvent}, HostRun (HLinked2.logG g) (s, L) ds st' →
      (∀ ev ∈ L, ev ∈ st'.2) ∧ ∀ (k : Fin n) (ws us : List IVal),
        (⟨(k, .vals ws), some (.vals us)⟩ : Σ _ : (sigN n).Op, Option Payload) ∈ ds →
          logEntry k ws us ∈ st'.2
  | [], _, _, _, h => by
    cases h
    exact ⟨fun _ h => h, fun _ _ _ h => nomatch h⟩
  | ⟨q, R⟩ :: ds, s, L, st', h => by
    cases h with
    | cons hd hr =>
      rename_i s₁
      obtain ⟨k₀, ws₀, hq, hR⟩ := hd
      subst hq
      cases R with
      | none =>
        obtain ⟨-, rfl⟩ := hR
        obtain ⟨h₁, h₂⟩ := log_sup hr
        refine ⟨h₁, fun k ws us hm => ?_⟩
        rcases List.mem_cons.mp hm with he | hm
        · simp at he
        · exact h₂ k ws us hm
      | some p =>
        cases p with
        | flat _ => exact hR.elim
        | vals us₀ =>
          obtain ⟨r, hg, hr'⟩ := Option.map_eq_some_iff.mp hR
          obtain ⟨s₂, L₂⟩ := s₁
          simp only [Prod.mk.injEq] at hr'
          obtain ⟨hr₁, rfl, rfl⟩ := hr'
          obtain ⟨h₁, h₂⟩ := log_sup hr
          refine ⟨fun ev hev => h₁ ev (List.mem_append_left _ hev), fun k ws us hm => ?_⟩
          rcases List.mem_cons.mp hm with he | hm
          · simp only [Sigma.mk.injEq, Prod.mk.injEq, Payload.vals.injEq, heq_eq_eq,
              Option.some.injEq] at he
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
            exact h₁ _ (List.mem_append_right _ (by simp [logEntry, hr₁]))
          · exact h₂ k ws us hm

/-! ## Moves of session plays -/

theorem ask_mem_callMoves {E F : Sig.{0}} :
    ∀ {ds : List (Σ m : E.Op, E.Ar m)} {d : Σ m : E.Op, E.Ar m}, d ∈ ds →
      (.inl (.ask d.1) : Move E F) ∈ callMoves ds
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ h => .tail _ (.tail _ (ask_mem_callMoves h))

/-- **Every host call of a session is asked in its play.** -/
theorem ask_mem_sessMoves (l : HLinked2) :
    ∀ {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
      {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))},
      calls.length = outs.length → calls.length = hs.length →
      ∀ d ∈ hs.flatten, (.inl (.ask d.1) : Move (sigN l.host.length) (sigN l.toComp.exports.length)) ∈ l.sessMoves calls outs hs
  | [], _, [], _, _, _, h => nomatch h
  | [], _, _ :: _, _, h, _, _ => nomatch h
  | _ :: _, [], _, h, _, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, h, _, _ => nomatch h
  | (j, vs) :: cs, o :: os, h :: hs, h₁, h₂, d, hd => by
    simp only [HLinked2.sessMoves]
    rcases List.mem_append.mp (List.flatten_cons ▸ hd) with hd | hd
    · exact .tail _ (List.mem_append_left _ (ask_mem_callMoves hd))
    · exact .tail _ (List.mem_append_right _ (.tail _
        (ask_mem_sessMoves l (by simpa using h₁) (by simpa using h₂) d hd)))

/-! ## Acceptance -/

variable {P : Profile} {prof : Silmaril.Wasm.Component.ProfileKind} {l : HLinked2} {s₀ : σ}
  {a : Fin l.host.length} {w : List UInt8}

theorem sessAccepted_iff (hl : l.Adequate) (hT : l.HostTyped g) :
    HLinked2.SessAcceptedRef P prof l g s₀ a w ↔ HLinked2.SessAcceptedIR P l g s₀ a w := by
  constructor
  · rintro ⟨calls, ht, p, hp, ev, hev, hfn, hb⟩
    rw [HLinked2.sessAdequacy_full P prof hl g hT s₀ calls ht] at hp
    obtain ⟨outs, hs, -, hlen, hlen', hmem, hrun⟩ := hp
    rcases log_sub hrun ev hev with h | ⟨d, hd, k, ws, us, rfl, rfl⟩
    · exact absurd h List.not_mem_nil
    · have hk : k = a := Fin.ext (by simpa [logEntry] using hfn)
      subst hk
      refine ⟨calls, ht, outs, hs, p.2, hlen, hlen', hmem, hrun, _, hd, ws, us, rfl, ?_⟩
      rw [← bytesOf?_map_toRefVal]
      exact hb
  · rintro ⟨calls, ht, outs, hs, st', hlen, hlen', hmem, hrun, d, hd, ws, us, rfl, hb⟩
    refine ⟨calls, ht, (refOuts outs, st'), ?_, logEntry a ws us,
      (log_sup hrun).2 a ws us hd, rfl, ?_⟩
    · rw [HLinked2.sessAdequacy_full P prof hl g hT s₀ calls ht]
      exact ⟨outs, hs, rfl, hlen, hlen', hmem, hrun⟩
    · simp only [logEntry]
      rw [bytesOf?_map_toRefVal]
      exact hb

theorem sessAcceptedIR_sub (h : HLinked2.SessAcceptedIR P l g s₀ a w) :
    w ∈ posBytesLang (l.toComp.den (impSem P)) a := by
  obtain ⟨calls, -, outs, hs, -, hlen, hlen', hmem, -, d, hd, ws, us, rfl, hb⟩ := h
  exact ⟨_, hmem, ws, ask_mem_sessMoves l hlen hlen' _ hd, hb⟩

end Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSession
