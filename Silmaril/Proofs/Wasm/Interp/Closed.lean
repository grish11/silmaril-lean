module

public import Silmaril.Wasm.Interp.Closed.Defs
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-!
# Closed modules through the native interpreter (proofs)

General forms of the proofs first written for `Silmaril.Wasm.Interp.Example` and the wasmi
reproducer (`Silmaril.Proofs.Wasm.Wasmi.Repro`): a closed module that `prepare?` allocates
without a start function instantiates to that allocation at every profile and host
(`prepare?_sound`); its store is typed (`Instantiate.ok`); more fuel never changes a result of
`invokeRun`; and a terminating run determines `nbeh`. The header is
`Silmaril.Wasm.Interp.Closed.Thms`.
-/

namespace Silmaril.Proofs.Wasm.Interp.Closed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.Closed

/-- A module that validates without imports and that `prepare?` allocates without a start
function instantiates to the allocation, at every profile and host. -/
theorem instantiate_of_prepare {m : Module} {p : Config Empty × Option FuncIdx}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : prepare? evalConst? ({} : Store Empty) m [] = some p) (hst : p.2 = none)
    (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) m [] p.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? m = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? m with _ | mt
    · simp [h] at hv
    · simp only [h, Option.map_some, Option.some.injEq] at hv
      exact ⟨mt, rfl, hv⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk m ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have h : Instantiate P host ({} : Store Empty) m [] (p.1.withStart p.2) :=
    (prepare?_sound (P := P) (host := host) (c := p.1) (st := p.2) evalConst?_evalSound
      hp hvalid).2
  have hw : p.1.withStart p.2 = p.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- The store of such an instance is typed. -/
theorem storeOk_of_prepare {m : Module} {p : Config Empty × Option FuncIdx}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : prepare? evalConst? ({} : Store Empty) m [] = some p) (hst : p.2 = none) :
    StoreOk p.1.store := by
  have hc : ConfigOk p.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (instantiate_of_prepare hv hp hst (SingleThreaded.profile fun _ _ _ _ => false)
        SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

/-- What `closed? m = true` says, unpacked. -/
theorem closed_spec {m : Module} (h : closed? m = true) :
    ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true ∧
      prepare? evalConst? ({} : Store Empty) m [] = some (prep m) ∧
      (prep m).1.code = [] ∧ (prep m).2 = none := by
  unfold closed? at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hv, hp⟩ := h
  refine ⟨hv, ?_⟩
  rcases hq : prepare? evalConst? ({} : Store Empty) m [] with _ | p
  · rw [hq] at hp
    cases hp
  · rw [hq] at hp
    simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
    have hprep : prep m = p := by simp [prep, hq]
    exact ⟨by rw [hprep], by rw [hprep]; exact hp.1, by rw [hprep]; exact hp.2⟩

theorem instantiate {m : Module} (h : closed? m = true) (P : Numerics.Profile)
    (host : HostSemantics Empty) : Instantiate P host ({} : Store Empty) m [] (prep m).1 :=
  let ⟨hv, hp, _, hst⟩ := closed_spec h
  instantiate_of_prepare hv hp hst P host

theorem storeOk {m : Module} (h : closed? m = true) : StoreOk (store m) :=
  let ⟨hv, hp, _, hst⟩ := closed_spec h
  storeOk_of_prepare hv hp hst

theorem nativeCheck_spec {m : Module} (h : nativeCheck m = true) :
    closed? m = true ∧ Binaryen.NativeFuncsOk (store m).funcs ∧ StoreChk (store m).funcs := by
  unfold nativeCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, nativeFuncsOk_of_check h.1.2, storeChk_of_check h.2⟩

theorem callOk_spec {m : Module} {a : Nat} {vs : List Val} (h : callOk m a vs = true) :
    nativeCheck m = true ∧ InvokeOk (store m) a vs := by
  unfold callOk at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, invokeOk?_sound h.2⟩

theorem adequacy {m : Module} {a : Nat} {vs : List Val} (h : callOk m a vs = true)
    (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store m) a vs = Binaryen.nbeh (store m) a vs :=
  let ⟨hn, hok⟩ := callOk_spec h
  let ⟨hc, hF, hS⟩ := nativeCheck_spec hn
  native_adequacy (P := P) (storeOk hc) hF hS hok

/-- More fuel never changes a result of `invokeRun`. -/
theorem invokeRun_mono {H : Type} {n n' : Nat} (hle : n ≤ n') {s : Store H} {a : Nat}
    {vs : List Val} {r : Store H × Binaryen.Flow} (h : Binaryen.invokeRun n s a vs = some r) :
    Binaryen.invokeRun n' s a vs = some r := by
  unfold Binaryen.invokeRun at h ⊢
  split at h
  · split at h
    · rename_i fn _ rs _ _
      rcases hr : Binaryen.run n s _ [] (Binaryen.liftInstrs fn.body) with _ | x
      · rw [hr] at h
        cases h
      · rw [hr] at h
        rw [Binaryen.run_mono hle hr]
        exact h
    · cases h
  · cases h

/-- The native behaviours of a terminating invocation are its single result. -/
theorem nbeh_eq_singleton {H : Type} {s : Store H} {a : Nat} {vs : List Val} {n : Nat}
    {b : Behaviour Val} (h : ((Binaryen.invokeRun n s a vs).bind fun r => Binaryen.flowBeh r.2) =
      some b) : Binaryen.nbeh s a vs = {b} := by
  obtain ⟨⟨s₀, fl₀⟩, h₀, hb₀⟩ := Option.bind_eq_some_iff.mp h
  ext b'
  constructor
  · rintro (⟨m, s₁, fl₁, h₁, hb₁⟩ | ⟨-, hdiv⟩)
    · have e₀ : Binaryen.invokeRun (max n m) s a vs = some (s₀, fl₀) :=
        invokeRun_mono (Nat.le_max_left n m) h₀
      have e₁ : Binaryen.invokeRun (max n m) s a vs = some (s₁, fl₁) :=
        invokeRun_mono (Nat.le_max_right n m) h₁
      have hfl : fl₁ = fl₀ := by
        rw [e₀] at e₁
        exact (Prod.mk.inj (Option.some.inj e₁)).2.symm
      have hb : some b' = some b := by rw [← hb₁, ← hb₀, hfl]
      exact Option.some.inj hb
    · rw [hdiv n] at h₀
      cases h₀
  · rintro rfl
    exact .inl ⟨n, s₀, fl₀, h₀, hb₀⟩

theorem behaviours_eq {m : Module} {a : Nat} {vs : List Val} {fuel : Nat} {b : Behaviour Val}
    (h : callOk m a vs = true) (hr : run m fuel a vs = some b) (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store m) a vs = {b} := by
  rw [adequacy h P]
  exact nbeh_eq_singleton hr

end Silmaril.Proofs.Wasm.Interp.Closed
