module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Run
public import Silmaril.Proofs.Wasm.Component.Reference.InstLink

/-!
# The instantiation results of `LinkedG.toRef`, read back

* `lrun_noHost`: a live run has no host event;
* `instBehaviours_of_lrun`: if the instantiation of `lg.toRef` after its host event is a live run
  to a configuration `m₂` with the host in control, not locked down, observing the root instance
  `0` and the export map `xs`, then its instantiation results are exactly that instance, as
  `instBehavioursL_toRef` of `Linked2`: every run after the host event that ends with the host in
  control or locked down is the live run (`lrun_end`), and a divergence would diverge from `m₂`,
  where the host is in control;
* `instBehavioursG_toRef`: for an exporter meeting `InitU`, the instantiation results of
  `lg.toRef` under any host functions are exactly the instance at `afterG` (`instG_lrun`);
* `afterG_waiting`: the configuration after instantiation has no waiting thread.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {σ : Type} {lg : LinkedG} {d : lg.exp.RefData P}

/-- **A live run has no host event.** -/
theorem lrun_noHost {E : CoreEngine} {prof : ProfileKind} {hr : HostReady σ}
    {D : Call E → Canon.P E σ (Ret E)} {m m₂ : Machine.Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr D m tr m₂) : ∀ ev, Label.host ev ∉ tr := by
  induction h with
  | refl => exact fun _ h => nomatch h
  | cons hl s _ ih =>
    intro ev hm
    rcases List.mem_cons.1 hm with e | hm
    · subst e
      exact hl.1 (Step.host_ready s.1).1
    · exact ih ev hm

/-- **The instantiation results of `lg.toRef`, from a live run after its host event.** -/
theorem instBehaviours_of_lrun {prof : ProfileKind} {impl : HostImpl (core3P P) σ} {h₀ : σ}
    {tr : List (Label (core3P P) σ)} {m₂ : Machine.Config (core3P P) σ}
    {xs : List (String × FuncId)}
    (d' : LRun prof (linkHost impl).hr (linkHost impl).dispatch (instStartG lg h₀) tr m₂)
    (hc : m₂.ctl = []) (hl : m₂.store.lockdown = false)
    (ho : traceObs tr = [instantiatedObs ⟨0⟩ xs]) :
    instBehaviours prof (linkHost impl) (initConfig h₀) lg.toRef [] = {.instance m₂ ⟨0⟩ xs} := by
  ext res
  refine ⟨fun hres => ?_, fun hres => ?_⟩
  · cases res with
    | «instance» m' inst es' =>
      show InstResult.instance m' inst es' = _
      obtain ⟨tr', hs, hn, hc', -, hobs⟩ := hres
      obtain ⟨m₃, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
      have he : m₃ = instStartG lg h₀ := hostRun_inv s₁
      obtain ⟨htr, hm⟩ := lrun_end d' hc (he ▸ hs₁) hn (.inl hc')
      have hdec : (traceObs tr').findSome? decodeInstantiated? = some (⟨0⟩, xs) := by
        rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
      have hie : (inst, es') = ((⟨0⟩ : InstId), xs) := Option.some.inj (hobs.symm.trans hdec)
      rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
    | traps =>
      obtain ⟨m', tr', hs, hn, -, ht⟩ := hres
      obtain ⟨m₃, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
      have he : m₃ = instStartG lg h₀ := hostRun_inv s₁
      obtain ⟨-, rfl⟩ := lrun_end d' hc (he ▸ hs₁) hn (.inr ht)
      have ht' : m'.store.lockdown = true := ht
      rw [hl] at ht'
      cases ht'
    | diverges =>
      obtain ⟨m₃, s₁, dv⟩ := hres
      have he : m₃ = instStartG lg h₀ := hostRun_inv s₁
      exact absurd (d'.diverges (he ▸ dv)) (not_diverges_of_ctl_nil hc)
  · rw [Set.mem_singleton_iff.1 hres]
    have s₀ : Machine.Step prof (linkHost impl).hr (linkHost impl).dispatch (initConfig h₀)
        (.host (instantiateTop lg.toRef [])) (instStartG lg h₀) :=
      Step.hostRun ⟨rfl, rfl, rfl⟩
    refine ⟨tr, .cons s₀ d'.steps, lrun_noHost d', hc, hl, ?_⟩
    rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]

/-- **The instantiation results of `lg.toRef`** are exactly the instance at `afterG`. -/
theorem instBehavioursG_toRef (hInit : d.InitU) (hFr : d.Frame) (hW : lg.WireTy)
    (hIg : lg.imp.Good) (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii) (prof : ProfileKind)
    (impl : HostImpl (core3P P) σ) (h₀ : σ) :
    ∃ (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl) (F : CoreFoot)
      (es : List (String × ItemVal (core3P P))) (r : Store (CanonHost (core3P P) × Nat)),
      InitW d pl F es (startG h₀) m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
      TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
      instBehaviours prof (linkHost impl) (initConfig h₀) lg.toRef [] =
        {.instance (afterG lg Ii m₁ r) ⟨0⟩ (exportMapG lg m₁.store.funcs.length)} := by
  obtain ⟨trD, m₁, pl, F, es, r, hA, hrs, hh, d', ho⟩ :=
    instG_lrun (prof := prof) (impl := impl) hInit hFr hW hIg hIi hIa hseg hNI hI h₀
  exact ⟨m₁, pl, F, es, r, hA, hrs, hh, instBehaviours_of_lrun d' rfl hA.lock ho⟩

/-- **No waiting thread after instantiation.** -/
theorem afterG_waiting {Ii : Silmaril.Wasm.Game.ScalarInstance} {h₀ : σ}
    {m₁ : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} {r : Store (CanonHost (core3P P) × Nat)}
    (hA : InitW d pl F es (startG h₀) m₁) : (afterG lg Ii m₁ r).store.waiting = [] := by
  have e : (afterG lg Ii m₁ r).store.waiting = m₁.store.waiting := rfl
  rw [e, hA.waiting]
  rfl

/-- **The instantiation of `lg.toRef`, publicly**: its results are exactly one instance, at a
configuration with the host in control and no waiting thread, with the root instance `0` and the
importer's exports at consecutive functions. -/
theorem instBehavioursG_eq (hInit : d.InitU) (hFr : d.Frame) (hW : lg.WireTy)
    (hIg : lg.imp.Good) (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) (prof : ProfileKind)
    (impl : HostImpl (core3P P) σ) (h₀ : σ) :
    ∃ (m : Machine.Config (core3P P) σ) (fb : Nat), m.ctl = [] ∧ m.store.lockdown = false ∧
      m.store.waiting = [] ∧
      instBehaviours prof (linkHost impl) (initConfig h₀) lg.toRef [] =
        {.instance m ⟨0⟩ (lg.imp.exports.mapIdx fun i x => (x.name, (⟨fb + i⟩ : FuncId)))} := by
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨m₁, pl, F, es, r, hA, -, -, he⟩ :=
    instBehavioursG_toRef hInit hFr hW hIg hIi hIa hseg hNI hI prof impl h₀
  exact ⟨afterG lg Ii m₁ r, m₁.store.funcs.length, rfl, hA.lock, afterG_waiting hA, he⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
