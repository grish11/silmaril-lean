module

public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.Basic
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusRef

/-!
# The bounded linked fixture: proofs

* `SessRun.sessCalls`: a session with its final configuration is a `SessCalls` session;
* `runSess_sound`, `sessSummary_sound`: the executable session driver is sound for `SessRun`
  and `sessRunBehaviours` (through `Embedder.callTop_sound` and `instantiateRun_mem`);
* `sessBehaviours_of_run`: without imports, `sessRunBehaviours` gives `sessBehaviours`;
* the concrete facts of `linkedC` and `linkedHRef`: closed computations of the copied
  validator and drivers over `core3 neverFail` (`decide +kernel`), read back by the lemmas above.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSession

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.LinkedSession
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Proofs.Wasm.Component.Reference.Litmus (exists_of_accepts)

section Drivers

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- A session with its final configuration is a session. -/
theorem SessRun.sessCalls {prof : ProfileKind} {h : Host E σ} {m m' : Machine.Config E σ}
    {k : Nat} {cs : List (FuncId × List Reference.Val)} {outs : List (Option (List Reference.Val))}
    (hr : SessRun prof h m k cs outs m') : SessCalls prof h m k cs outs := by
  induction hr with
  | nil m k => exact .nil m k
  | ret hc _ ih => exact .ret hc ih
  | trap hc _ ih => exact .trap hc ih

/-- **The executable session driver is sound.** -/
theorem runSess_sound (emb : Embedder E σ) (o : Oracle E) (fuel : Nat) :
    ∀ {m m' : Machine.Config E σ} {k : Nat} {cs : List (FuncId × List Reference.Val)}
      {outs : List (Option (List Reference.Val))}, runSess emb o fuel m k cs = some (outs, m') →
      SessRun o.prof (Host.ofEmbedder emb) m k cs outs m'
  | m, m', k, [], outs, h => by
    simp only [runSess, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil _ _
  | m, m', k, (f, args) :: cs, outs, h => by
    simp only [runSess] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i rs ho
        obtain ⟨⟨os, mm⟩, hp, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .ret (emb.callTop_sound o hr ho) (runSess_sound emb o fuel hp)
      · rename_i ho
        obtain ⟨⟨os, mm⟩, hp, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .trap (emb.callTop_sound o hr ho) (runSess_sound emb o fuel hp)
      · cases h

/-- **The executable session summary is sound** for `sessRunBehaviours`. -/
theorem sessSummary_sound {emb : Embedder E σ} {o : Oracle E} {fuel : Nat}
    {c : CompAst E.Module} {ims : Iface} {σ0 : σ} {calls : List (String × List Reference.Val)}
    {p : List (Option (List Reference.Val)) × σ} (h : sessSummary emb o fuel c ims σ0 calls = some p) :
    p ∈ sessRunBehaviours o.prof (Host.ofEmbedder emb) σ0 c ims calls := by
  unfold sessSummary at h
  obtain ⟨⟨r, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fs, hfs, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h₂
  exact ⟨r.config, inst, es, fs, q.2, instantiateRun_mem emb o hi, hfs,
    runSess_sound emb o fuel hq, rfl⟩

/-- Without imports, the session outcomes of `sessRunBehaviours` are `sessBehaviours`. -/
theorem sessBehaviours_of_run {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {c : CompAst E.Module} {calls : List (String × List Reference.Val)}
    {p : List (Option (List Reference.Val)) × σ} (hp : p ∈ sessRunBehaviours prof h σ0 c [] calls) :
    p.1 ∈ sessBehaviours prof h σ0 c calls := by
  obtain ⟨m₀, inst, es, fs, m', hi, hfs, hr, -⟩ := hp
  exact ⟨m₀, inst, es, fs, hi, hfs, SessRun.sessCalls hr⟩

/-- A session behaviour comes from an instantiation of the component. -/
theorem inst_of_sessRun {prof : ProfileKind} {h : Host E σ} {σ0 : σ} {c : CompAst E.Module}
    {ims : Iface} {calls : List (String × List Reference.Val)} {p : List (Option (List Reference.Val)) × σ}
    (hp : p ∈ sessRunBehaviours prof h σ0 c ims calls) :
    ∃ m inst es, InstResult.instance m inst es ∈
      instBehaviours prof h (hostConfig ims σ0) c (importArgs ims) := by
  obtain ⟨m₀, inst, es, -, -, hi, -⟩ := hp
  exact ⟨m₀, inst, es, hi⟩

end Drivers

/-! ## The concrete facts -/

/-- The value `u32 n` of the reference machine. -/
abbrev u32 (n : BitVec 32) : Reference.Val := toRefVal (.u32 n)

theorem linkedC_valid : ∃ ct, check? Features.p2 linkedC.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

theorem linkedHRef_valid : ∃ ct, check? Features.p2 linkedHRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

theorem linkedC_pokePeek_run : ([none, some [u32 1]], 0) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedC.toRef []
      [("poke", []), ("peek", [])] :=
  sessSummary_sound (emb := embCount) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedC_poke_run : ([none], 0) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedC.toRef [] [("poke", [])] :=
  sessSummary_sound (emb := embCount) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedC_peek_run : ([some [u32 0]], 0) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedC.toRef [] [("peek", [])] :=
  sessSummary_sound (emb := embCount) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedC_poke_traps :
    callTraps embCount first 400 linkedC.toRef [] 0 "poke" [] = some [.coreTrap] := by
  decide +kernel

theorem linkedH_pokePeek_run : ([none, some [u32 1]], 0) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedHRef hostIface
      [("poke", []), ("peek", [])] :=
  sessSummary_sound (emb := embCount) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedH_ping_run : ([some []], 1) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedHRef hostIface
      [("ping", [])] :=
  sessSummary_sound (emb := embCount) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedH_all_run : ([none, some [u32 1], some []], 1) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedHRef hostIface
      [("poke", []), ("peek", []), ("ping", [])] :=
  sessSummary_sound (emb := embCount) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedH_silent_run : ([none, some [u32 1], none], 0) ∈
    sessRunBehaviours first.prof (Host.ofEmbedder embSilent) 0 linkedHRef hostIface
      [("poke", []), ("peek", []), ("ping", [])] :=
  sessSummary_sound (emb := embSilent) (o := first) (fuel := 400) (by decide +kernel)

theorem linkedH_silent_ping_traps :
    callTraps embSilent first 400 linkedHRef hostIface 0 "ping" [] = some [.cannotBlockSync] := by
  decide +kernel

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSession
