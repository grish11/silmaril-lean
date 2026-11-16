module

public import Silmaril.Wasi.Component.Accept.Strict.Defs
public import Silmaril.Wasi.Component.Accept.Reject.Thms
public import Silmaril.Semantics.Accept.Verdict.Thms
public import Silmaril.Wasi.Component.Accept.Acceptor.Defs

/-! # Components: some play accepts and no play rejects: theorems

* **One runner**: the exported combined set is `acceptsSafely (exportRun σ dec) (retWith acc
  true) (retWith rej false)` (`exportAcceptedNotRejected_eq_acceptsSafely`). The imported one
  is `acceptsSafely (importRun σ dec) (reqOf acc) (reqOf rej)`
  (`importAcceptedNotRejected_eq_acceptsSafely`). Both quantifiers range over the plays of the
  same strategy.
* **Equivalence invariance**: equal named traces, hence `CompEquiv` IR components under any
  layout, give equal combined sets (`exportAcceptedNotRejected_eq_of_traces`, …).
* **No monotonicity claim**: refinement removes plays, which can remove the accepting witness
  or the rejecting run, so the combined set moves in neither direction. Counterexamples are in
  `Silmaril.Wasi.Accept.Examples` (`not_mono_refinement`, `not_anti_refinement`). The parts
  are one-sided: acceptance shrinks under refinement (`exportAccepted_mono`), and
  never-rejection grows (`neverFalse_anti`).
* **One function for both verdicts**: an import used for both accepting and rejecting gives the
  empty set (`importAcceptedNotRejected_self`, from `acceptsSafely_eq_empty_of_subset`). An
  export used for both is different: its accepting and rejecting outcomes (returns of `true` and
  `false`) never conflict (`retWith_conflicts`), so its combined set consists of the values on
  which it returns `true` in some play and `false` in none.
* **Wrappers**: `ComponentAcceptor.strictLang_eq_acceptsSafely_exp` and `…_imp`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val Comp CoreModule)
open Silmaril.Wasm.Component.Algebra (CompEquiv)

variable {I X I' X' : Set FnName} {α : Type} {dec : List Val → Option α} {acc rej : FnName}

theorem mem_exportAccepted_iff_events {σ : Strategy (nsig I) (nsig X)} {a : α} :
    a ∈ exportAccepted σ acc dec ↔
      ∃ t ∈ Traces σ, ∃ args, .ret acc args (some [.bool true]) ∈ t ∧ dec args = some a := by
  simp only [exportAccepted, observed, Set.mem_ofPred_eq, exportObs_eq_some]
  constructor
  · rintro ⟨t, ht, e, he, args, rfl, hd⟩; exact ⟨t, ht, args, he, hd⟩
  · rintro ⟨t, ht, args, he, hd⟩; exact ⟨t, ht, _, he, args, rfl, hd⟩

theorem mem_exportRejected_iff_events {σ : Strategy (nsig I) (nsig X)} {a : α} :
    a ∈ exportRejected σ rej dec ↔
      ∃ t ∈ Traces σ, ∃ args, .ret rej args (some [.bool false]) ∈ t ∧ dec args = some a := by
  simp only [exportRejected, observed, Set.mem_ofPred_eq, exportFalseObs_eq_some]
  constructor
  · rintro ⟨t, ht, e, he, args, rfl, hd⟩; exact ⟨t, ht, args, he, hd⟩
  · rintro ⟨t, ht, args, he, hd⟩; exact ⟨t, ht, _, he, args, rfl, hd⟩

theorem mem_importAccepted_iff_events {σ : Strategy (nsig I) (nsig X)} {f : FnName} {a : α} :
    a ∈ importAccepted σ f dec ↔ ∃ t ∈ Traces σ, ∃ args, .req f args ∈ t ∧ dec args = some a := by
  simp only [importAccepted, observed, Set.mem_ofPred_eq, importObs_eq_some]
  constructor
  · rintro ⟨t, ht, e, he, args, rfl, hd⟩; exact ⟨t, ht, args, he, hd⟩
  · rintro ⟨t, ht, args, he, hd⟩; exact ⟨t, ht, _, he, args, rfl, hd⟩

/-- **The exported combined set is `acceptsSafely` of one runner.** -/
theorem exportAcceptedNotRejected_eq_acceptsSafely (σ : Strategy (nsig I) (nsig X)) :
    exportAcceptedNotRejected σ acc rej dec =
      Silmaril.Accept.acceptsSafely (exportRun σ dec) (retWith acc true) (retWith rej false) := by
  ext a
  simp only [exportAcceptedNotRejected, neverFalse, Set.mem_inter_iff, Set.mem_compl_iff,
    mem_exportAccepted_iff_events, mem_exportRejected_iff_events, Silmaril.Accept.acceptsSafely,
    Silmaril.Accept.mem_acceptsSome, Silmaril.Accept.mem_neverRejects, exportRun, retWith,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨t, ht, args, he, hd⟩, hn⟩
    refine ⟨⟨_, ⟨⟨t, ht, he⟩, hd⟩, args, rfl⟩, ?_⟩
    rintro e ⟨⟨t', ht', he'⟩, hd'⟩ ⟨args', rfl⟩
    exact hn ⟨t', ht', args', he', hd'⟩
  · rintro ⟨⟨e, ⟨⟨t, ht, he⟩, hd⟩, args, rfl⟩, hn⟩
    refine ⟨⟨t, ht, args, he, hd⟩, ?_⟩
    rintro ⟨t', ht', args', he', hd'⟩
    exact hn _ ⟨⟨t', ht', he'⟩, hd'⟩ ⟨args', rfl⟩

/-- **The imported combined set is `acceptsSafely` of one runner.** -/
theorem importAcceptedNotRejected_eq_acceptsSafely (σ : Strategy (nsig I) (nsig X)) :
    importAcceptedNotRejected σ acc rej dec =
      Silmaril.Accept.acceptsSafely (importRun σ dec) (reqOf acc) (reqOf rej) := by
  ext a
  simp only [importAcceptedNotRejected, neverCalled, importRejected, Set.mem_inter_iff,
    Set.mem_compl_iff, mem_importAccepted_iff_events, Silmaril.Accept.acceptsSafely,
    Silmaril.Accept.mem_acceptsSome, Silmaril.Accept.mem_neverRejects, importRun, reqOf,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨t, ht, args, he, hd⟩, hn⟩
    refine ⟨⟨_, ⟨⟨t, ht, he⟩, hd⟩, args, rfl⟩, ?_⟩
    rintro e ⟨⟨t', ht', he'⟩, hd'⟩ ⟨args', rfl⟩
    exact hn ⟨t', ht', args', he', hd'⟩
  · rintro ⟨⟨e, ⟨⟨t, ht, he⟩, hd⟩, args, rfl⟩, hn⟩
    refine ⟨⟨t, ht, args, he, hd⟩, ?_⟩
    rintro ⟨t', ht', args', he', hd'⟩
    exact hn _ ⟨⟨t', ht', he'⟩, hd'⟩ ⟨args', rfl⟩

/-! ## Equivalence invariance -/

theorem exportAcceptedNotRejected_eq_of_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    exportAcceptedNotRejected σ acc rej dec = exportAcceptedNotRejected τ acc rej dec := by
  unfold exportAcceptedNotRejected
  rw [exportAccepted_eq_of_traces h, neverFalse_eq_of_traces h]

theorem importAcceptedNotRejected_eq_of_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    importAcceptedNotRejected σ acc rej dec = importAcceptedNotRejected τ acc rej dec := by
  unfold importAcceptedNotRejected
  rw [importAccepted_eq_of_traces h, neverCalled_eq_of_traces h]

section IR

variable {M : Type} [CoreModule M] (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout)
  {c c' : Comp M}

theorem exportAcceptedNotRejected_compModel_of_compEquiv (h : CompEquiv C c c') :
    exportAcceptedNotRejected (L.compModel C c) acc rej dec =
      exportAcceptedNotRejected (L.compModel C c') acc rej dec := by
  unfold Layout.compModel; rw [h.2]

theorem importAcceptedNotRejected_compModel_of_compEquiv (h : CompEquiv C c c') :
    importAcceptedNotRejected (L.compModel C c) acc rej dec =
      importAcceptedNotRejected (L.compModel C c') acc rej dec := by
  unfold Layout.compModel; rw [h.2]

end IR

/-! ## Wrappers -/

/-- The strict language of an exported acceptor with a reject function is the combined set. -/
theorem ComponentAcceptor.strictLang_exp (A : ComponentAcceptor) {r : FnName}
    (hr : A.reject = some r) (hm : A.mode = .exp) :
    A.strictLang = exportAcceptedNotRejected A.model A.accept r (args1 bytes?) := by
  simp [ComponentAcceptor.strictLang, ComponentAcceptor.lang, ComponentAcceptor.neverRejectedLang,
    hr, hm, exportAcceptedNotRejected, exportBytesLang]
  rfl

/-- The strict language of an imported acceptor with a reject function is the combined set. -/
theorem ComponentAcceptor.strictLang_imp (A : ComponentAcceptor) {r : FnName}
    (hr : A.reject = some r) (hm : A.mode = .imp) :
    A.strictLang = importAcceptedNotRejected A.model A.accept r (args1 bytes?) := by
  simp [ComponentAcceptor.strictLang, ComponentAcceptor.lang, ComponentAcceptor.neverRejectedLang,
    hr, hm, importAcceptedNotRejected, bytesLang]
  rfl

/-! ## One function for both verdicts -/

/-- **One import for both verdicts**: nothing is accepted and never rejected. -/
theorem importAcceptedNotRejected_self (σ : Strategy (nsig I) (nsig X)) :
    importAcceptedNotRejected σ acc acc dec = ∅ := by
  rw [importAcceptedNotRejected_eq_acceptsSafely]
  exact Silmaril.Accept.acceptsSafely_eq_empty_of_subset subset_rfl

/-- Returns of `true` and of `false` never conflict, even for the same export. -/
theorem retWith_conflicts (f g : FnName) :
    Silmaril.Accept.conflicts (retWith f true) (retWith g false) = ∅ := by
  ext e
  simp only [Silmaril.Accept.conflicts, retWith, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false, not_and, forall_exists_index]
  rintro args rfl ⟨args', h⟩
  simp at h

/-! ## Wrappers as `acceptsSafely` -/

theorem ComponentAcceptor.strictLang_eq_acceptsSafely_exp (A : ComponentAcceptor) {r : FnName}
    (hr : A.reject = some r) (hm : A.mode = .exp) :
    A.strictLang = Silmaril.Accept.acceptsSafely (exportRun A.model (args1 bytes?))
      (retWith A.accept true) (retWith r false) := by
  rw [A.strictLang_exp hr hm, exportAcceptedNotRejected_eq_acceptsSafely]

theorem ComponentAcceptor.strictLang_eq_acceptsSafely_imp (A : ComponentAcceptor) {r : FnName}
    (hr : A.reject = some r) (hm : A.mode = .imp) :
    A.strictLang = Silmaril.Accept.acceptsSafely (importRun A.model (args1 bytes?))
      (reqOf A.accept) (reqOf r) := by
  rw [A.strictLang_imp hr hm, importAcceptedNotRejected_eq_acceptsSafely]

/-- An imported acceptor rejecting through its accepting import has an empty strict language. -/
theorem ComponentAcceptor.strictLang_imp_self (A : ComponentAcceptor)
    (hr : A.reject = some A.accept) (hm : A.mode = .imp) : A.strictLang = ⊥ := by
  rw [A.strictLang_imp hr hm, importAcceptedNotRejected_self]; rfl

end Silmaril.Wasi.Accept
