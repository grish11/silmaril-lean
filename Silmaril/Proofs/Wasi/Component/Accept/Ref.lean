module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Wasm.Component.Conformance.Run.Thms
public import Silmaril.Wasm.Component.Reference.Embedding.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.Thms`: the executable acceptor driver is
sound for `Accepted`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.Ref

open Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem steps_append {prof : ProfileKind} {hr : HostReady AcceptSt}
    {d : Call E → P E AcceptSt (Ret E)} {m₁ m₂ m₃ : Config E AcceptSt}
    {t₁ t₂ : List (Label E AcceptSt)} (h₁ : Steps prof hr d m₁ t₁ m₂)
    (h₂ : Steps prof hr d m₂ t₂ m₃) : Steps prof hr d m₁ (t₁ ++ t₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

/-- With no deferred host work, `untilLoop` adds only internal labels and `tick`s. -/
theorem untilLoop_env (c : CallId) (n : Nat) (st : o.State) (m : Config E AcceptSt)
    (acc : List (Label E AcceptSt)) :
    ∃ tr, (Conformance.untilLoop noReady dispatch X o (fun _ => false) (pure .unit) c n st m
        acc).labels = acc.reverse ++ tr ∧
      ∀ l ∈ tr, (∀ ev, l ≠ .host ev) ∨ l = .host .tick := by
  induction n generalizing st m acc with
  | zero => exact ⟨[], by simp [Conformance.untilLoop], by simp⟩
  | succ n ih =>
    by_cases hd : Conformance.callDone c m = true
    · exact ⟨[], by simp [Conformance.untilLoop, hd], by simp⟩
    cases e : step? dispatch X (o.at st) m with
    | some p =>
      obtain ⟨l, st', m'⟩ := p
      obtain ⟨tr, h₁, h₂⟩ := ih st' m' (l :: acc)
      refine ⟨l :: tr, ?_, ?_⟩
      · simp only [Conformance.untilLoop, hd, e, h₁, List.reverse_cons, List.append_assoc,
          List.singleton_append, Bool.false_eq_true, ↓reduceIte]
      · intro l' hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · exact .inl (step?_not_host noReady dispatch X o e)
        · exact h₂ l' hl'
    | none =>
      by_cases w : wantsTick noReady m = true
      · cases e' : hostStep? noReady .tick m with
        | none => exact ⟨[], by simp [Conformance.untilLoop, hd, e, w, e'], by simp⟩
        | some p =>
          obtain ⟨l, m'⟩ := p
          obtain ⟨tr, h₁, h₂⟩ := ih st m' (l :: acc)
          have hl : l = .host .tick := hostStep?_label e'
          refine ⟨l :: tr, ?_, ?_⟩
          · simp only [Conformance.untilLoop, hd, e, w, e', h₁, List.reverse_cons,
              List.append_assoc, List.singleton_append, Bool.false_eq_true, ↓reduceIte]
          · intro l' hl'
            rcases List.mem_cons.mp hl' with rfl | hl'
            · exact .inr hl
            · exact h₂ l' hl'
      · exact ⟨[], by simp [Conformance.untilLoop, hd, e, w], by simp⟩

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem envLabel_of {es : List (String × FuncId)} {l : Label E AcceptSt}
    (h : (∀ ev, l ≠ .host ev) ∨ l = .host .tick) : EnvLabel es l := by
  rcases h with h | rfl
  · cases l with
    | host ev => exact absurd rfl (h ev)
    | _ => trivial
  · trivial

theorem mem_snd_of_lookup {es : List (String × FuncId)} {name : String} {f : FuncId}
    (h : es.lookup name = some f) : f ∈ es.map Prod.snd := by
  induction es with
  | nil => simp at h
  | cons p es ih =>
    obtain ⟨n', f'⟩ := p
    by_cases hn : name = n'
    · subst hn; simp [List.lookup] at h; subst h; simp
    · have : es.lookup name = some f := by
        have hb : (name == n') = false := beq_false_of_ne hn
        simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (ih this)

/-- `runCalls` is a run of environment moves. -/
theorem runCalls_sound (fuel : Nat) (es : List (String × FuncId)) :
    ∀ (k : Nat) (calls : List (String × List Value.Val)) (m m' : Config E AcceptSt),
      runCalls X o fuel es k calls m = some m' →
      ∃ tr, Steps o.prof noReady dispatch m tr m' ∧ ∀ l ∈ tr, EnvLabel es l
  | _, [], m, m', h => by
    simp only [runCalls, Option.some.injEq] at h
    exact ⟨[], h ▸ .refl _, by simp⟩
  | k, (name, args) :: rest, m, m', h => by
    simp only [runCalls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨f, hf, r, hr, hrest⟩ := h
    obtain ⟨tr, h₁, h₂⟩ := runCalls_sound fuel es (k + 1) rest r.config m' hrest
    have hs := Conformance.callUntil_sound noReady dispatch X o (fun _ => false) (pure .unit) hr
    unfold Conformance.callUntil at hr
    cases e : hostStep? noReady (.invoke ⟨k⟩ f args) m with
    | none => simp [e] at hr
    | some p =>
      obtain ⟨l, m₁⟩ := p
      have hl : l = .host (.invoke ⟨k⟩ f args) := hostStep?_label e
      have hr' : Conformance.untilLoop noReady dispatch X o (fun _ => false) (pure .unit) ⟨k⟩
          fuel o.state m₁ [l] = r := by simpa [e] using hr
      obtain ⟨tr', h₃, h₄⟩ := untilLoop_env X o ⟨k⟩ fuel o.state m₁ [l]
      rw [hr'] at h₃
      refine ⟨r.labels ++ tr, steps_append hs h₁, ?_⟩
      intro l' hl'
      rcases List.mem_append.mp hl' with hl' | hl'
      · rw [h₃] at hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · rw [hl]; exact mem_snd_of_lookup hf
        · exact envLabel_of (h₄ l' (by simpa using hl'))
      · exact h₂ l' hl'

/-- **Soundness of `acceptRun`**: a recorded byte list is accepted. -/
theorem acceptRun_sound {fuel : Nat} {c : Syntax.Component E.Module}
    {calls : List (String × List Value.Val)} {st : AcceptSt}
    (h : acceptRun X o fuel c calls = some st) {w : List UInt8} (hw : [bytesVal w] ∈ st) :
    Accepted o.prof c w := by
  unfold acceptRun at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨l, m₁⟩, h₁, ⟨inst, es⟩, h₂, m, h₃, h₄⟩ := h
  have hl : l = .host (.run (acceptLinkedProg c)) := hostStep?_label h₁
  have hs₁ := Machine.hostStep?_sound o.prof noReady dispatch h₁
  have hrun := Machine.run_sound noReady dispatch X o fuel m₁
  obtain ⟨tr, htr, henv⟩ := runCalls_sound X o fuel es 0 calls _ m h₃
  refine ⟨_, _, inst, es, tr, m, ?_, run_noHost noReady dispatch X o fuel m₁, h₂, htr,
    henv, ?_⟩
  · rw [← hl]; exact .cons hs₁ hrun
  · have h₅ : m.host = st := Option.some.inj h₄
    exact h₅ ▸ hw

end Silmaril.Proofs.Wasi.Component.Accept.Ref
