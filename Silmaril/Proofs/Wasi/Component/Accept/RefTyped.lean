module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Proofs.Wasi.Component.Accept.Ref
public import Silmaril.Wasm.Component.Reference.Thms

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.Typed.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.Ref

open Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

variable {E : CoreEngine}

theorem typedEnvLabel_envLabel {m₁ : Config E AcceptSt} {es : List (String × FuncId)}
    {l : Label E AcceptSt} (h : TypedEnvLabel m₁ es l) : EnvLabel es l := by
  cases l with
  | host ev => cases ev <;> simp_all [TypedEnvLabel, EnvLabel]
  | _ => trivial

theorem acceptedTyped_accepted [∀ a b, Decidable (E.ExternSub a b)] {prof : ProfileKind}
    {c : Syntax.Component E.Module} {w : List UInt8} (h : AcceptedTyped prof c w) :
    Accepted prof c w :=
  let ⟨tr₀, m₁, inst, es, tr, m₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  ⟨tr₀, m₁, inst, es, tr, m₂, h₁, h₂, h₃, h₄, fun l hl => typedEnvLabel_envLabel (h₅ l hl), h₆⟩

theorem acceptedExportTyped_acceptedExport [∀ a b, Decidable (E.ExternSub a b)]
    {prof : ProfileKind} {c : Syntax.Component E.Module} {w : List UInt8}
    (h : AcceptedExportTyped prof c w) : AcceptedExport prof c w :=
  let ⟨m₁, inst, es, f, _, hi, hf, _, _, _, hc⟩ := h
  Or.inl ⟨m₁, inst, es, f, hi, hf, hc⟩

variable [∀ a b, Decidable (E.ExternSub a b)] (X : E.Exec) (o : Oracle E)

theorem runCallsTyped_sound (fuel : Nat) (m₁ : Config E AcceptSt)
    (es : List (String × FuncId)) :
    ∀ (k : Nat) (calls : List (String × List Value.Val)) (m m' : Config E AcceptSt),
      runCallsTyped X o fuel m₁ es k calls m = some m' →
      ∃ tr, Steps o.prof noReady dispatch m tr m' ∧ ∀ l ∈ tr, TypedEnvLabel m₁ es l
  | _, [], m, m', h => by
    simp only [runCallsTyped, Option.some.injEq] at h
    exact ⟨[], h ▸ .refl _, by simp⟩
  | k, (name, args) :: rest, m, m', h => by
    simp only [runCallsTyped, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨f, hf, ft, hft, h⟩ := h
    by_cases ht : argsTyped ft args = true
    · simp only [ht, ↓reduceIte, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, hrest⟩ := h
      obtain ⟨tr, h₁, h₂⟩ := runCallsTyped_sound fuel m₁ es (k + 1) rest r.config m' hrest
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
          · rw [hl]; exact ⟨mem_snd_of_lookup hf, ft, hft, ht⟩
          · rcases h₄ l' (by simpa using hl') with h | rfl
            · cases l' with
              | host ev => exact absurd rfl (h ev)
              | _ => trivial
            · trivial
        · exact h₂ l' hl'
    · simp [ht] at h

theorem recordsTyped_of_run {fuel : Nat} {ft : WIT.FuncType Empty RtId}
    {c : Syntax.Component E.Module}
    {calls : List (String × List Value.Val)} {st : AcceptSt}
    (h : acceptRunTyped X o fuel c calls ft = some st) {args : List Value.Val} (hw : args ∈ st) :
    RecordsTyped ft o.prof c args := by
  unfold acceptRunTyped at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨l, m₁⟩, h₁, ⟨inst, es⟩, h₂, m, h₃, h₄⟩ := h
  have hl : l = .host (.run (acceptLinkedProgAt ft c)) := hostStep?_label h₁
  have hs₁ := hostStep?_sound o.prof noReady dispatch h₁
  have hrun := Machine.run_sound noReady dispatch X o fuel m₁
  obtain ⟨tr, htr, henv⟩ := runCallsTyped_sound X o fuel _ es 0 calls _ m h₃
  refine ⟨_, _, inst, es, tr, m, ?_, run_noHost noReady dispatch X o fuel m₁, h₂, htr,
    henv, ?_⟩
  · rw [← hl]; exact .cons hs₁ hrun
  · have h₅ : m.host = st := Option.some.inj h₄
    exact h₅ ▸ hw

theorem acceptRunTyped_sound {fuel : Nat} {c : Syntax.Component E.Module}
    {calls : List (String × List Value.Val)} {st : AcceptSt}
    (h : acceptRunTyped X o fuel c calls = some st) {w : List UInt8}
    (hw : [bytesVal w] ∈ st) : AcceptedTyped o.prof c w :=
  recordsTyped_of_run X o h hw

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem bytesOf?_bytesVal (w : List UInt8) : bytesOf? [bytesVal w] = some w := by
  have h : ∀ b : UInt8, u8Of? (.int .u8 (b.toNat : Int)) = some b := by
    intro b
    have hb := b.toNat_lt
    have hc : (0:Int) ≤ ↑b.toNat ∧ (↑b.toNat : Int) < 256 := ⟨by omega, by omega⟩
    simp only [u8Of?, hc, and_self, ↓reduceIte, Int.toNat_natCast, Option.some.injEq]
    exact UInt8.ofNat_toNat
  simp only [bytesOf?, bytesVal]
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.mapM_cons, List.map_cons, h b] at ih ⊢
    simp [ih]

theorem acceptedTyped_bytes {prof : ProfileKind} {c : Syntax.Component E.Module}
    {w : List UInt8} (h : AcceptedTyped prof c w) : AcceptedTypedBytes acceptFT prof c w :=
  ⟨[bytesVal w], h, bytesOf?_bytesVal w⟩

theorem acceptedExportTyped_of_run {fuel fuel' : Nat} {c : Syntax.Component E.Module}
    {w : List UInt8} {r₁ : RunResult E AcceptSt o.State} {inst : InstId}
    {es : List (String × FuncId)} {f : FuncId} {ft : WIT.FuncType Empty RtId}
    {r : RunResult E AcceptSt o.State}
    (hi : (emb X).instantiateRun o fuel c [] (Silmaril.Wasm.Component.Reference.initConfig []) =
      some (r₁, inst, es))
    (hf : es.lookup "accept" = some f) (hft : funcFT? r₁.config f = some ft)
    (hty : argsTyped ft [bytesVal w] = true) (hres : ft.result = some (.prim .bool))
    (hc : (emb X).callTop o fuel' ⟨0⟩ f [bytesVal w] r₁.config = some r)
    (ho : callOutcome? ⟨0⟩ r = some (.resolved (some [.bool true]))) :
    AcceptedExportTyped o.prof c w :=
  ⟨r₁.config, inst, es, f, ft, Silmaril.Wasm.Component.Reference.instantiateRun_mem (emb X) o hi,
    hf, hft, hty, hres, Silmaril.Wasm.Component.Reference.callTop_mem (emb X) o hc ho⟩

end Silmaril.Proofs.Wasi.Component.Accept.Ref
