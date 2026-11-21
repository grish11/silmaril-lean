module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Wasm.Component.Conformance.Run.Thms
public import Silmaril.Wasm.Component.Reference.Embedding.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.Thms`: the executable acceptor driver is
sound for `RecordsWith`, for every environment policy; policy monotonicity; the bytes
systems. -/

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
theorem envMove_of {allowed : FuncId → List Value.Val → Prop} {l : Label E AcceptSt}
    (h : (∀ ev, l ≠ .host ev) ∨ l = .host .tick) : EnvMove allowed l := by
  rcases h with h | rfl
  · cases l with
    | host ev => exact absurd rfl (h ev)
    | _ => trivial
  · trivial

/-- `runCallsWith` is a run of moves of the policy `P`. -/
theorem runCallsWith_sound (P : EnvPolicy E) (fuel : Nat) (m₁ : Config E AcceptSt)
    (es : List (String × FuncId)) :
    ∀ (k : Nat) (calls : List (String × List Value.Val)) (m m' : Config E AcceptSt),
      runCallsWith X o P fuel m₁ es k calls m = some m' →
      ∃ tr, Steps o.prof noReady dispatch m tr m' ∧ ∀ l ∈ tr, P.Label m₁ es l
  | _, [], m, m', h => by
    simp only [runCallsWith, Option.some.injEq] at h
    exact ⟨[], h ▸ .refl _, by simp⟩
  | k, (name, args) :: rest, m, m', h => by
    simp only [runCallsWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨f, _, h⟩ := h
    by_cases ht : P.check m₁ es f args = true
    · simp only [ht, ↓reduceIte, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, hrest⟩ := h
      obtain ⟨tr, h₁, h₂⟩ := runCallsWith_sound P fuel m₁ es (k + 1) rest r.config m' hrest
      have hs := Conformance.callUntil_sound noReady dispatch X o (fun _ => false) (pure .unit) hr
      unfold Conformance.callUntil at hr
      cases e : hostStep? noReady (.invoke ⟨k⟩ f args) m with
      | none => simp [e] at hr
      | some p =>
        obtain ⟨l, m₂⟩ := p
        have hl : l = .host (.invoke ⟨k⟩ f args) := hostStep?_label e
        have hr' : Conformance.untilLoop noReady dispatch X o (fun _ => false) (pure .unit) ⟨k⟩
            fuel o.state m₂ [l] = r := by simpa [e] using hr
        obtain ⟨tr', h₃, h₄⟩ := untilLoop_env X o ⟨k⟩ fuel o.state m₂ [l]
        rw [hr'] at h₃
        refine ⟨r.labels ++ tr, steps_append hs h₁, ?_⟩
        intro l' hl'
        rcases List.mem_append.mp hl' with hl' | hl'
        · rw [h₃] at hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · rw [hl]; exact P.check_sound _ _ _ _ ht
          · exact envMove_of (h₄ l' (by simpa using hl'))
        · exact h₂ l' hl'
    · simp [ht] at h

/-- **Soundness of the executable driver**, for every policy and every `accept` type: an
argument list recorded by `acceptRunWith` is recorded in `RecordsWith`. -/
theorem recordsWith_of_run (P : EnvPolicy E) {fuel : Nat} {c : Syntax.Component E.Module}
    {calls : List (String × List Value.Val)} {ft : WIT.FuncType Empty RtId} {st : AcceptSt}
    (h : acceptRunWith X o P fuel c calls ft = some st) {args : List Value.Val}
    (hw : args ∈ st) : RecordsWith P ft o.prof c args := by
  unfold acceptRunWith at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨l, m₁⟩, h₁, ⟨inst, es⟩, h₂, m, h₃, h₄⟩ := h
  have hl : l = .host (.run (acceptLinkedProgAt ft c)) := hostStep?_label h₁
  have hs₁ := Machine.hostStep?_sound o.prof noReady dispatch h₁
  have hrun := Machine.run_sound noReady dispatch X o fuel m₁
  obtain ⟨tr, htr, henv⟩ := runCallsWith_sound X o P fuel _ es 0 calls _ m h₃
  refine ⟨_, _, inst, es, tr, m, ?_, run_noHost noReady dispatch X o fuel m₁, h₂, htr,
    henv, ?_⟩
  · rw [← hl]; exact .cons hs₁ hrun
  · have h₅ : m.host = st := Option.some.inj h₄
    exact h₅ ▸ hw

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem envMove_mono {a b : FuncId → List Value.Val → Prop} (hab : ∀ f args, a f args → b f args)
    {l : Label E AcceptSt} (h : EnvMove a l) : EnvMove b l := by
  cases l with
  | host ev => cases ev <;> first | exact hab _ _ h | trivial
  | _ => trivial

/-- **Policy monotonicity**: a larger environment records more. -/
theorem recordsWith_mono {P Q : EnvPolicy E} (hPQ : P ≤ Q) {ft : WIT.FuncType Empty RtId}
    {prof : ProfileKind} {c : Syntax.Component E.Module} {args : List Value.Val}
    (h : RecordsWith P ft prof c args) : RecordsWith Q ft prof c args :=
  let ⟨tr₀, m₁, inst, es, tr, m₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  ⟨tr₀, m₁, inst, es, tr, m₂, h₁, h₂, h₃, h₄,
    fun l hl => envMove_mono (hPQ m₁ es) (h₅ l hl), h₆⟩

theorem bytesSystemWith_of_decode {P : EnvPolicy Eng} {prof : ProfileKind} {b : ByteArray}
    {w : List UInt8} {a : RefAcceptor prof} (h : decodeValid b = some a) :
    bytesSystemWith P prof b w ↔ AcceptedWith P prof a.comp w :=
  ⟨fun ⟨_, ha', hw⟩ => by
      obtain ⟨a'', h'', rfl⟩ := Option.map_eq_some_iff.mp ha'
      rw [h] at h''; cases h''; exact hw,
    fun hw => ⟨⟨a.comp⟩, by simp [h], hw⟩⟩

theorem bytesSystemWith_of_decode_none {P : EnvPolicy Eng} {prof : ProfileKind} {b : ByteArray}
    {w : List UInt8} (h : decodeValid (prof := prof) b = none) : ¬ bytesSystemWith P prof b w :=
  fun ⟨_, ha, _⟩ => by simp [h] at ha

theorem bytesSystemWith_iff {P : EnvPolicy Eng} {prof : ProfileKind} {b : ByteArray}
    {w : List UInt8} : bytesSystemWith P prof b w ↔
      ∃ a : RefAcceptor prof, decodeValid b = some a ∧ AcceptedWith P prof a.comp w := by
  refine ⟨fun h => ?_, fun ⟨_, ha, hw⟩ => (bytesSystemWith_of_decode ha).2 hw⟩
  cases hd : decodeValid (prof := prof) b with
  | none => exact absurd h (bytesSystemWith_of_decode_none hd)
  | some a => exact ⟨a, rfl, (bytesSystemWith_of_decode hd).1 h⟩

end Silmaril.Proofs.Wasi.Component.Accept.Ref
