module

public import Silmaril.Wasm.Abstract.LinkCore.Defs
public import Silmaril.Wasm.Abstract.PubModule.Thms
public import Silmaril.Wasm.Abstract.PubModuleXP.Thms
public import Silmaril.Games.Abstract.StratHost.Thms

/-!
# The closed Core semantics of invocations, host inside (proofs)

* `steps_iff_evRun`: a Core run is a labelled run at some log;
* `diverges_iff`: Core divergence with the host is host-free divergence after a labelled run, a
  labelled run to a callout the host diverges on, or a productive run;
* `linkT_div_iff`, `linkT_mem_iff`: the divergent and the other behaviours of the link of an
  observation triple `obsTriple Ok O` whose divergence clauses are those of Core (`CoreObsL`,
  `CoreObsLXP` agree there) and whose call prefixes are reached callouts;
* `linkT_coreTriple`, `linkT_coreTripleXP`: the link of the Core triples is the closed Core
  triple.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.LinkCore

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratHost
  Silmaril.Wasm.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Core runs and divergence -/

theorem steps_evRun {c c' : Config H} (h : Steps P host c c') : ∃ cs, EvRun P host c cs c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .refl _⟩
  | head hs _ ih =>
    obtain ⟨cs, h⟩ := ih
    obtain ⟨e, he⟩ := step_hEvStep hs
    cases e with
    | none => exact ⟨cs, .silent he h⟩
    | some e => exact ⟨e :: cs, .event he h⟩

theorem steps_iff_evRun {c c' : Config H} : Steps P host c c' ↔ ∃ cs, EvRun P host c cs c' :=
  ⟨steps_evRun, fun ⟨_, h⟩ => evRun_steps h⟩

theorem diverges_of_steps {c d : Config H} (h : Steps P host c d) (hd : Diverges P host d) :
    Diverges P host c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hd
  | head hs _ ih => exact Silmaril.InfiniteTrace.fold hs ih

theorem diverges_of_noHost {c : Config H} (h : Diverges P (fun _ _ _ _ => False) c) :
    Diverges P host c := by
  obtain ⟨tr, h0, hs⟩ := h
  exact ⟨tr, h0, fun n => Step.host_mono (fun _ _ _ _ h => h.elim) (hs n)⟩

theorem diverges_of_atCallout {c : Config H} {m : (wasmHostSig H).Op} (hc : AtCallout c m)
    (hd : host m.1 m.2.1 m.2.2 .diverged) : Diverges P host c := by
  obtain ⟨E, b, hdec, hs⟩ := hc
  have hst : Step P host c c :=
    hEvStep_step (e := none) (.inr ⟨rfl, E, b, m.1, m.2.2, hdec, by rw [hs]; exact hd⟩)
  exact ⟨fun _ => c, rfl, fun _ => hst⟩

/-- **Core divergence with the host, by its host events.** -/
theorem diverges_iff {c : Config H} :
    Diverges P host c ↔
      (∃ cs c', EvRun P host c cs c' ∧ Diverges P (fun _ _ _ _ => False) c') ∨
      (∃ cs c', EvRun P host c cs c' ∧ ∃ m, AtCallout c' m ∧ host m.1 m.2.1 m.2.2 .diverged) ∨
      ∃ ω, CoreInf P host c ω := by
  constructor
  · intro h
    rcases diverges_events.1 h with ⟨cs, c', hr, hq⟩ | hω
    · rcases quiet_iff.1 hq with hd | ⟨d, hfree, E, a, hh, us, hdec, hd⟩
      · exact .inl ⟨cs, c', hr, hd⟩
      · refine .inr (.inl ⟨cs, d, ?_, (hh, d.store, us), ⟨E, a, hdec, rfl⟩, hd⟩)
        simpa using evRun_trans hr (evRun_of_free hfree)
    · exact .inr (.inr hω)
  · rintro (⟨cs, c', hr, hd⟩ | ⟨cs, c', hr, m, hat, hd⟩ | ⟨ω, hω⟩)
    · exact diverges_of_steps (evRun_steps hr) (diverges_of_noHost hd)
    · exact diverges_of_steps (evRun_steps hr) (diverges_of_atCallout hat hd)
    · exact coreInf_diverges hω

/-! ## Linking an observation triple with Core divergence clauses -/

section Link

variable {Ok : Store H → Nat × List Val → Prop} {O : Store H → Nat × List Val → FullObs H → Prop}

/-- **The divergence of the link**: the linked triple diverges exactly when the Core run does. -/
theorem linkT_div_iff
    (hsat : ∀ s q x, x ∈ StratObs.satP (obsTriple Ok O) s q →
      Ok s q ∧ ∃ c, EvRun P host (invoke s q.1 q.2) x.1 c ∧ AtCallout c x.2)
    (hdone : ∀ s q cs, ¬ O s q (.done cs .div))
    (hdiv : ∀ s q cs, O s q (.div cs) ↔
      ∃ c, EvRun P host (invoke s q.1 q.2) cs c ∧ Diverges P (fun _ _ _ _ => False) c)
    (hhd : ∀ s q cs (m : (wasmHostSig H).Op), host m.1 m.2.1 m.2.2 .diverged →
      (∃ c, EvRun P host (invoke s q.1 q.2) cs c ∧ AtCallout c m) → O s q (.hostDiv cs m))
    (hprod : ∀ s q ω, O s q (.prod ω) ↔ CoreInf P host (invoke s q.1 q.2) ω)
    (s : Store H) (q : Nat × List Val) (c₀ : List (Call Sig.empty)) :
    (c₀, End.div) ∈ (linkT (coreHostRel host) (obsTriple Ok O)).1 s q ↔
      Ok s q ∧ Diverges P host (invoke s q.1 q.2) := by
  constructor
  · rintro (⟨c, ⟨hq, hd | ⟨-, hd⟩⟩, -⟩ | ⟨-, ⟨c, m, ⟨hp, -, -⟩, hm⟩ | ⟨ω, ⟨hq, hω⟩, -⟩⟩)
    · exact (hdone _ _ _ hd).elim
    · obtain ⟨c', hr, hc'⟩ := (hdiv _ _ _).1 hd
      exact ⟨hq, diverges_iff.2 (.inl ⟨c, c', hr, hc'⟩)⟩
    · obtain ⟨hq, c', hr, hat⟩ := hsat s q _ hp
      exact ⟨hq, diverges_iff.2 (.inr (.inl ⟨c, c', hr, m, hat, hm⟩))⟩
    · exact ⟨hq, diverges_iff.2 (.inr (.inr ⟨ω, (hprod _ _ _).1 hω⟩))⟩
  · rintro ⟨hq, h⟩
    rcases diverges_iff.1 h with ⟨cs, c', hr, hd⟩ | ⟨cs, c', hr, m, hat, hm⟩ | ⟨ω, hω⟩
    · exact .inl ⟨cs, ⟨hq, .inr ⟨rfl, (hdiv _ _ _).2 ⟨c', hr, hd⟩⟩⟩, evRun_consistent hr⟩
    · exact .inr ⟨rfl, .inl ⟨cs, m,
        ⟨.inl ⟨hq, .inr (hhd s q cs m hm ⟨c', hr, hat⟩)⟩, evRun_consistent hr, .inr hm⟩, hm⟩⟩
    · exact .inr ⟨rfl, .inr ⟨ω, ⟨hq, (hprod _ _ _).2 hω⟩, coreInf_consistent hω⟩⟩

/-- **The other behaviours of the link** are the finished observations at some log. -/
theorem linkT_mem_iff
    (hcons : ∀ s q cs e, O s q (.done cs e) → (coreHostRel host).Consistent cs)
    {e : End (Store H) (List Val ⊕ Nat)} (he : e ≠ .div)
    (s : Store H) (q : Nat × List Val) (c₀ : List (Call Sig.empty)) :
    (c₀, e) ∈ (linkT (coreHostRel host) (obsTriple Ok O)).1 s q ↔
      Ok s q ∧ ∃ cs, O s q (.done cs e) := by
  constructor
  · rintro (⟨c, ⟨hq, hd | ⟨he', -⟩⟩, -⟩ | ⟨he', -⟩)
    · exact ⟨hq, c, hd⟩
    · exact (he he').elim
    · exact (he he').elim
  · rintro ⟨hq, cs, hd⟩
    exact .inl ⟨cs, ⟨hq, .inl hd⟩, hcons _ _ _ _ hd⟩

end Link

/-! ## The Core triples -/

theorem coreObsL_cons {s : Store H} {q : Nat × List Val} {cs : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} (h : CoreObsL P host s q.1 q.2 (.done cs e)) :
    (coreHostRel host).Consistent cs := by
  rcases e with ⟨_ | _, _⟩ | _ | _
  · exact evRun_consistent h
  · exact h.elim
  · exact evRun_consistent h.choose_spec
  · exact h.elim

theorem coreObsLXP_cons {s : Store H} {q : Nat × List Val} {cs : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} (h : CoreObsLXP P host s q.1 q.2 (.done cs e)) :
    (coreHostRel host).Consistent cs := by
  rcases e with ⟨_ | _, _⟩ | _ | _
  · exact evRun_consistent h
  · exact evRun_consistent h
  · exact evRun_consistent h.choose_spec
  · exact h.elim

theorem coreObsL_done_iff {s : Store H} {q : Nat × List Val} {e : End (Store H) (List Val ⊕ Nat)}
    (he : e ≠ .div) : (∃ cs, CoreObsL P host s q.1 q.2 (.done cs e)) ↔ closedEnd P host s q e := by
  rcases e with ⟨_ | _, _⟩ | _ | _
  · exact steps_iff_evRun.symm
  · exact ⟨fun ⟨_, h⟩ => h, False.elim⟩
  · exact ⟨fun ⟨_, s₂, h⟩ => ⟨s₂, evRun_steps h⟩,
      fun ⟨s₂, h⟩ => (steps_evRun h).imp fun _ h => ⟨s₂, h⟩⟩
  · exact (he rfl).elim

theorem coreObsLXP_done_iff {s : Store H} {q : Nat × List Val}
    {e : End (Store H) (List Val ⊕ Nat)} (he : e ≠ .div) :
    (∃ cs, CoreObsLXP P host s q.1 q.2 (.done cs e)) ↔ closedEndXP P host s q e := by
  rcases e with ⟨_ | _, _⟩ | _ | _
  · exact steps_iff_evRun.symm
  · exact steps_iff_evRun.symm
  · exact ⟨fun ⟨_, s₂, h⟩ => ⟨s₂, evRun_steps h⟩,
      fun ⟨s₂, h⟩ => (steps_evRun h).imp fun _ h => ⟨s₂, h⟩⟩
  · exact (he rfl).elim

/-- **The link of the Core triple is the closed Core triple.** -/
theorem linkT_coreTriple {Ok : Store H → Nat × List Val → Prop} :
    linkT (coreHostRel host) (coreTriple P host Ok) = closedCore P host Ok := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  funext s q
  ext ⟨c₀, e⟩
  by_cases he : e = .div
  · subst he
    exact linkT_div_iff (fun _ _ _ h => coreTriple_satP_callout h) (fun _ _ _ h => h)
      (fun _ _ _ => Iff.rfl)
      (fun _ _ _ ⟨_, _, _⟩ hd ⟨c, hr, E, b, hdec, hs⟩ => ⟨c, E, b, hr, hdec, hs, hd⟩)
      (fun _ _ _ => Iff.rfl) s q c₀
  · exact (linkT_mem_iff (fun _ _ _ _ h => coreObsL_cons h) he s q c₀).trans
      (and_congr_right fun _ => coreObsL_done_iff he)

/-- **The link of the Core triple with exceptions is the closed Core triple with exceptions.** -/
theorem linkT_coreTripleXP {Ok : Store H → Nat × List Val → Prop} :
    linkT (coreHostRel host) (coreTripleXP P host Ok) = closedCoreXP P host Ok := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  funext s q
  ext ⟨c₀, e⟩
  by_cases he : e = .div
  · subst he
    exact linkT_div_iff (fun _ _ _ h => coreTripleXP_satP_callout h) (fun _ _ _ h => h)
      (fun _ _ _ => Iff.rfl)
      (fun _ _ _ ⟨_, _, _⟩ hd ⟨c, hr, E, b, hdec, hs⟩ => ⟨c, E, b, hr, hdec, hs, hd⟩)
      (fun _ _ _ => Iff.rfl) s q c₀
  · exact (linkT_mem_iff (fun _ _ _ _ h => coreObsLXP_cons h) he s q c₀).trans
      (and_congr_right fun _ => coreObsLXP_done_iff he)

end Silmaril.Proofs.Wasm.Abstract.LinkCore
