module

public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms

/-!
# Splitting a logged prefix followed by host-free divergence at a handler (proofs)

The handler analogues of `HostCall.diverges_label_seq_split` and `HostCall.evDiv_label_seq_split`:

* `diverges_handler_seq_split`: an infinite host-free run of a handler in place diverges in its
  body, or the body runs to a stuck end and the handler around that end diverges;
* `evDiv_handler_seq_split`: a labelled run with the events `cs`, then host-free divergence, of a
  handler in place: the body diverges with the whole log, or runs to a stuck end that is not at a
  host call with a prefix of the log, and the handler around that end goes on with the rest.

The labelled-run split is `evRunN_handler_seq_split` (`HostClosingXP`); a handler exit form is a
label exit form (`handlerExit_labelExit`), so it has no step and is not at a host call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Bookkeeping -/

/-- A configuration with an answered host call has no host-free step. -/
theorem noFree_of_event {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P host c (some e) c') : ∀ c'', ¬ Step P Det.noHost c c'' := by
  obtain ⟨E, a, hd, -⟩ := h
  exact fun c'' => noFree_of_decompose hd

theorem evRunN_append {k k' : Nat} {c c₁ c₂ : Config H} {cs₁ cs₂ : List (Call (wasmHostSig H))}
    (h₁ : EvRunN P host k c cs₁ c₁) (h₂ : EvRunN P host k' c₁ cs₂ c₂) :
    EvRunN P host (k + k') c (cs₁ ++ cs₂) c₂ := by
  induction h₁ with
  | refl => simpa using h₂
  | silent hs _ ih =>
    have := EvRunN.silent hs (ih h₂)
    rwa [show ∀ a b : Nat, a + 1 + b = a + b + 1 from fun a b => by omega]
  | event hs _ ih =>
    have := EvRunN.event hs (ih h₂)
    rw [show ∀ a b : Nat, a + 1 + b = a + b + 1 from fun a b => by omega]
    simpa using this

/-- A host-free run is a labelled run with no event. -/
theorem evRunN_of_closed {c c' : Config H} (h : Steps P (fun _ _ _ _ => False) c c') :
    ∃ k, EvRunN P host k c [] c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .silent (Or.inl hs) hk⟩

/-- A run to a host call, its answer, and a host-free run after it. -/
theorem evRunN_event_closed {k : Nat} {c c₀ c₁ c₂ : Config H}
    {cs : List (Call (wasmHostSig H))} {e : Call (wasmHostSig H)}
    (h : EvRunN P host k c cs c₀) (he : HEvStep P host c₀ (some e) c₁)
    (h₂ : Steps P (fun _ _ _ _ => False) c₁ c₂) : ∃ k', EvRunN P host k' c (cs ++ [e]) c₂ := by
  obtain ⟨k₂, hk₂⟩ := evRunN_of_closed (host := host) h₂
  exact ⟨_, evRunN_append h (.event he hk₂)⟩

/-! ## Handlers -/

theorem decompose?_handler_some {s : Store H} {n : Nat} {cs : List Catch} {b : List Admin}
    {E : Ctx} {a : Nat} {hh : H} {us : List Val} (hd : decompose? s b = some (E, a, hh, us)) :
    decompose? s [.handler n cs b] = some (.handler [] n cs E [], a, hh, us) := by
  have hs : splitVals [Admin.handler n cs b] = ([], [.handler n cs b]) := by
    simp [splitVals, Admin.val?]
  rw [decompose?_of_split hs, decompHead_handler, hd]
  rfl

/-- **A labelled step lifts through a handler**, with the same label. -/
theorem hEvStep_handler {s s' : Store H} {f f' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat) (cs : List Catch)
    (h : HEvStep P host ⟨s, f, b⟩ l ⟨s', f', b'⟩) :
    HEvStep P host ⟨s, f, [.handler n cs b]⟩ l ⟨s', f', [.handler n cs b']⟩ := by
  cases l with
  | none =>
    rcases h with h | ⟨hc, E, a, hh, us, hd, hdiv⟩
    · exact .inl (Step.ctxtHandler h)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact .inr ⟨rfl, _, a, hh, us, decompose?_handler_some hd, hdiv⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hans, hc⟩ := h
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨_, a, decompose?_handler_some hd, hs, hans, by simp [Ctx.fill, vals]⟩

/-- **Label transfer**: a step `I ⟶ I'` whose labelled steps all lift to the labelled outer
step `O ⟶ O'` has the outer step's label. -/
theorem hEvStep_transfer {I I' O O' : Config H} {l : Option (Call (wasmHostSig H))}
    (hO : HEvStep P host O l O') (hI : Step P host I I')
    (hlift : ∀ l', HEvStep P host I l' I' → HEvStep P host O l' O') : HEvStep P host I l I' := by
  obtain ⟨l', h'⟩ := step_hEvStep hI
  obtain rfl := hEvStep_unique (hlift l' h') hO
  exact h'

/-- A handler exit form has no step. -/
theorem handlerExit_stuck {host' : HostSemantics H} {s : Store H} {f : Frame} {n : Nat}
    {cs : List Catch} {b out : List Admin} (h : HandlerExit s f n cs b out) (s' : Store H)
    (f' : Frame) : ∀ c', ¬ Step P host' ⟨s', f', b⟩ c' := by
  obtain ⟨out', hx⟩ := handlerExit_labelExit h
  exact fun c' => labelExit_stuck hx c'

/-- A handler exit form is not at a host call. -/
theorem handlerExit_decompose {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {b out : List Admin} (h : HandlerExit s f n cs b out) (s' : Store H) :
    decompose? s' b = none := by
  obtain ⟨out', hx⟩ := handlerExit_labelExit h
  exact decompose?_labelExit hx

/-- The handler's body runs to a stuck end, and the handler around it, in place, diverges. -/
def DivHandlerSeqAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (ws : List Val) (n : Nat) (cs₀ : List Catch)
    (b rest : List Admin) : Prop :=
  ∃ cb : Config H, Steps P host ⟨s, f, b⟩ cb ∧ (∀ c', ¬ Step P host cb c') ∧
    Diverges P host ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩

/-- **Splitting a divergent run of a handler in place**: the body diverges, or it runs to a
stuck end and the handler around that end diverges. -/
theorem diverges_handler_seq_split {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin}
    (h : Diverges P host ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩) :
    Diverges P host ⟨s, f, b⟩ ∨ DivHandlerSeqAfter P host s f ws n cs₀ b rest := by
  classical
  by_cases hA : DivHandlerSeqAfter P host s f ws n cs₀ b rest
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H =>
      Diverges P host ⟨c.store, c.frame, vals ws ++ [.handler n cs₀ c.code] ++ rest⟩ ∧
      ¬ DivHandlerSeqAfter P host c.store c.frame ws n cs₀ c.code rest) ?_ (a := ⟨s, f, b⟩)
    ⟨h, hA⟩
  rintro ⟨s, f, b⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
  · obtain ⟨c', hc', hd'⟩ := hd.unfold
    obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (X := .handler n cs₀ b) trivial (by simpa using hc')
    rcases Step.handler_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
    · refine ⟨⟨s', f', b'⟩, hin, by simpa [Diverges] using hd', ?_⟩
      rintro ⟨cb, h₁, hs₁, hk⟩
      exact hna ⟨cb, .head hin h₁, hs₁, hk⟩
    · obtain ⟨c', hc'⟩ := hb
      exact (handlerExit_stuck hex s f c' hc').elim
  · exact (hna ⟨⟨s, f, b⟩, .refl, fun c' h => hb ⟨c', h⟩, hd⟩).elim

/-- A handler around a body stuck at a host call has no step. -/
theorem handler_stuck_of_decompose {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {host' : HostSemantics H}
    (hb : ∀ c', ¬ Step P host' ⟨s, f, b⟩ c') (hd : (decompose? s b).isSome) :
    ∀ c', ¬ Step P host' ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ c' := by
  intro c' hc'
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .handler n cs₀ b) trivial (by simpa using hc')
  rcases Step.handler_inv h₀ with ⟨s', f', b', hin, -⟩ | ⟨out, hex, -⟩
  · exact hb _ hin
  · rw [handlerExit_decompose hex s] at hd
    cases hd

/-- An answered host call inside a handler is the body's answered host call. -/
theorem hEvStep_handler_inv {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {z : Config H} {e : Call (wasmHostSig H)}
    (hd : (decompose? s b).isSome)
    (h : HEvStep P host ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ (some e) z) :
    ∃ s' f' b', z = ⟨s', f', vals ws ++ [.handler n cs₀ b'] ++ rest⟩ ∧
      HEvStep P host ⟨s, f, b⟩ (some e) ⟨s', f', b'⟩ := by
  obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .handler n cs₀ b) trivial
    (by simpa using hEvStep_step h)
  rcases Step.handler_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
  · refine ⟨s', f', b', by simp [hz], hEvStep_transfer h hin fun l' h' => ?_⟩
    simpa [hz] using hEvStep_ctx ws rest (hEvStep_handler n cs₀ h')
  · rw [handlerExit_decompose hex s] at hd
    cases hd

/-- **Splitting a handler in place**: the body diverges with the whole log, or runs to a stuck
end that is not at a host call with a prefix of the log, and the handler around that end goes
on with the rest. -/
theorem evDiv_handler_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {cs : List (Call (wasmHostSig H))}
    (h : EvDiv P host N ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ cs) :
    EvDiv P host N ⟨s, f, b⟩ cs ∨
      ∃ (cb : Config H) (N₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))),
        cs = cs₁ ++ cs₂ ∧ m ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        EvDiv P host m ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩ cs₂ := by
  have hfree : ∀ (cb : Config H), (∀ c', ¬ Step P (fun _ _ _ _ => False) cb c') →
      Diverges P (fun _ _ _ _ => False)
        ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩ →
      decompose? cb.store cb.code = none := by
    intro cb hs hd
    cases hdc : decompose? cb.store cb.code with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨b', hb', -⟩ := hd.unfold
      exact handler_stuck_of_decompose (P := P) (ws := ws) (n := n) (cs₀ := cs₀) (rest := rest)
        (s := cb.store) (f := cb.frame) hs (by rw [hdc]; rfl) b' hb'
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₁₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · rcases diverges_handler_seq_split hd with hd' | ⟨cb, hst, hs, hd₁⟩
    · exact .inl (.inl ⟨rfl, hd'⟩)
    · obtain ⟨k, hk⟩ := evRunN_of_closed (host := host) hst
      exact .inr ⟨cb, k, N, [], [], rfl, le_refl _, hk, hs, hfree cb hs hd₁, .inl ⟨rfl, hd₁⟩⟩
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, hb, hsb, hk', hx⟩ :=
    evRunN_handler_seq_split hr (noFree_of_event he)
  cases hdc : decompose? cb.store cb.code with
  | none =>
    exact .inr ⟨cb, N₁, k - N₁, cs₁, cs₂ ++ [e], by simp, by omega, hb, hsb, hdc,
      .inr ⟨k - N₁, cs₂, e, c₀, c₁, le_refl _, rfl, hk', he, hd⟩⟩
  | some y =>
    have hsome : (decompose? cb.store cb.code).isSome := by rw [hdc]; rfl
    obtain ⟨rfl, rfl⟩ := hx hsome
    obtain ⟨s', f', b', rfl, he'⟩ := hEvStep_handler_inv hsome he
    rcases diverges_handler_seq_split hd with hd' | ⟨cb', hst, hs, hd₁⟩
    · exact .inl (.inr ⟨N₁, cs₁, e, cb, _, hN₁.trans hk, by simp, hb, he', hd'⟩)
    · obtain ⟨k', hk''⟩ := evRunN_event_closed hb he' hst
      exact .inr ⟨cb', k', 0, cs₁ ++ [e], [], by simp, Nat.zero_le _, hk'', hs,
        hfree cb' hs hd₁, .inl ⟨rfl, hd₁⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
