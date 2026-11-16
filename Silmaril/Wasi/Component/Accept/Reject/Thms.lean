module

public import Silmaril.Wasi.Component.Accept.Reject.Defs
public import Silmaril.Wasi.Component.Accept.Thms
public import Silmaril.Semantics.Accept.Rel.Thms

/-! # Rejection, never-rejection and indexed acceptance of components: theorems

* **Witnesses**: a value is rejected through the export iff some play ends in a `false`
  return of a call with that value (`mem_exportRejected_iff`).
* **Refinement** shrinks rejection and so grows never-rejection (`neverCalled_anti`,
  `neverFalse_anti`), while it shrinks acceptance (`importAccepted_mono`).
* **Equivalence**: equal named traces, and `CompEquiv` IR components under any layout, give
  equal never-rejected sets (`neverFalse_eq_of_traces`, `neverCalled_compModel_of_compEquiv`, …).
* **Indexed**: erasing the WIT-name index yields the values passed to some import
  (`eraseSome_importIndexed`), and a layout position indexes its import's set
  (`layoutIndexed_of_getElem?`).
* **Vacuity**: the bottom strategy (it never answers) never returns `false`, so it
  never-rejects every value (`exportRejected_bot`, `neverFalse_bot`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val Comp CoreModule)
open Silmaril.Wasm.Component.Algebra (CompEquiv CompRefines)

variable {I X I' X' : Set FnName} {α : Type} {f : FnName} {dec : List Val → Option α}

theorem exportFalseObs_eq_some {e : WEv} {a : α} :
    exportFalseObs f dec e = some a ↔
      ∃ args, e = .ret f args (some [.bool false]) ∧ dec args = some a := by
  constructor
  · intro h
    unfold exportFalseObs at h
    split at h
    · split_ifs at h with hg
      exact ⟨_, by rw [hg], h⟩
    · cases h
  · rintro ⟨args, rfl, h⟩
    simp [exportFalseObs, h]

theorem exportRejected_eq (σ : Strategy (nsig I) (nsig X)) :
    exportRejected σ f dec = σ.accepted (exportFalseObs f dec ∘ wev) :=
  observed_map wev fun _ => rfl

/-- **A value is rejected through the export `f` iff some play ends in a `false` return of a
call of `f` with it.** -/
theorem mem_exportRejected_iff (σ : Strategy (nsig I) (nsig X)) {a : α} :
    a ∈ exportRejected σ f dec ↔ ∃ s m, s ++ [m] ∈ σ.plays ∧
      ∃ args, wev m = .ret f args (some [.bool false]) ∧ dec args = some a := by
  rw [exportRejected_eq, Strategy.mem_accepted_iff]
  simp only [Function.comp_apply, exportFalseObs_eq_some]

theorem mem_neverFalse_iff (σ : Strategy (nsig I) (nsig X)) {a : α} :
    a ∈ neverFalse σ f dec ↔ ∀ s m, s ++ [m] ∈ σ.plays →
      ∀ args, wev m = .ret f args (some [.bool false]) → dec args ≠ some a := by
  simp only [neverFalse, Set.mem_compl_iff, mem_exportRejected_iff]
  push Not
  rfl

theorem mem_neverCalled_iff (σ : Strategy (nsig I) (nsig X)) {a : α} :
    a ∈ neverCalled σ f dec ↔ ∀ s m, s ++ [m] ∈ σ.plays →
      ∀ args, wev m = .req f args → dec args ≠ some a := by
  simp only [neverCalled, importRejected, Set.mem_compl_iff, mem_importAccepted_iff]
  push Not
  rfl

/-! ## Refinement and equivalence -/

theorem exportRejected_mono {σ τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) :
    exportRejected σ f dec ⊆ exportRejected τ f dec :=
  observed_mono (traces_mono h)

/-- A refinement calls `reject` with fewer values. -/
theorem neverCalled_anti {σ τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) :
    neverCalled τ f dec ⊆ neverCalled σ f dec :=
  Set.compl_subset_compl.2 (importAccepted_mono h)

/-- A refinement returns `false` on fewer values. -/
theorem neverFalse_anti {σ τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) :
    neverFalse τ f dec ⊆ neverFalse σ f dec :=
  Set.compl_subset_compl.2 (exportRejected_mono h)

theorem neverCalled_eq_of_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    neverCalled σ f dec = neverCalled τ f dec := by
  unfold neverCalled importRejected; rw [importAccepted_eq_of_traces h]

theorem neverFalse_eq_of_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    neverFalse σ f dec = neverFalse τ f dec := by
  unfold neverFalse exportRejected; rw [h]

section IR

variable {M : Type} [CoreModule M] (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout)
  {c c' : Comp M}

theorem neverCalled_compModel_of_compEquiv (h : CompEquiv C c c') :
    neverCalled (L.compModel C c) f dec = neverCalled (L.compModel C c') f dec := by
  unfold Layout.compModel; rw [h.2]

theorem neverFalse_compModel_of_compEquiv (h : CompEquiv C c c') :
    neverFalse (L.compModel C c) f dec = neverFalse (L.compModel C c') f dec := by
  unfold Layout.compModel; rw [h.2]

/-- A refining IR component never-rejects at least as much. -/
theorem neverFalse_compModel_of_compRefines (h : CompRefines C c c') :
    neverFalse (L.compModel C c') f dec ⊆ neverFalse (L.compModel C c) f dec :=
  neverFalse_anti (Layout.view_mono L h.2)

theorem neverCalled_compModel_of_compRefines (h : CompRefines C c c') :
    neverCalled (L.compModel C c') f dec ⊆ neverCalled (L.compModel C c) f dec :=
  neverCalled_anti (Layout.view_mono L h.2)

end IR

/-! ## Vacuity -/

/-- The bottom strategy never answers, so it rejects nothing. -/
theorem exportRejected_bot : exportRejected (⊥ : Strategy (nsig I) (nsig X)) f dec = ∅ := by
  ext a
  simp only [Set.mem_empty_iff_false, iff_false, mem_exportRejected_iff, not_exists, not_and]
  intro s m hs
  have h := Strategy.mem_bot.1 hs
  rcases s with _ | ⟨x, s⟩
  · simp only [List.nil_append] at h
    rcases h with h | ⟨q, hq⟩
    · cases h
    · rw [List.singleton_inj] at hq
      subst hq
      intro args he
      simp [wev] at he
  · rcases h with h | ⟨q, hq⟩
    · cases h
    · simp at hq

theorem neverFalse_bot : neverFalse (⊥ : Strategy (nsig I) (nsig X)) f dec = Set.univ := by
  rw [neverFalse, exportRejected_bot, Set.compl_empty]

/-! ## Indexed acceptance -/

/-- Erasing the WIT-name index: the values passed to some import. -/
theorem eraseSome_importIndexed (σ : Strategy (nsig I) (nsig X)) :
    Silmaril.Accept.eraseSome (importIndexed σ dec) = ⋃ g, importAccepted σ g dec := rfl

theorem layoutIndexed_of_getElem? (L : Layout) (σ : Strategy (nsig I) (nsig X)) {i : Nat}
    (h : L.imports[i]? = some f) : layoutIndexed L σ dec i = importAccepted σ f dec := by
  simp [layoutIndexed, h]

theorem layoutIndexed_of_le (L : Layout) (σ : Strategy (nsig I) (nsig X)) {i : Nat}
    (h : L.imports.length ≤ i) : layoutIndexed L σ dec i = ∅ := by
  simp [layoutIndexed, List.getElem?_eq_none h]

end Silmaril.Wasi.Accept
