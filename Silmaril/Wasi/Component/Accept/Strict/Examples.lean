module

public import Silmaril.Wasi.Component.Accept.Strict.Thms
import Silmaril.Proofs.Wasi.Component.Accept.Strict

/-! # Some play accepts and no play rejects: the cases

On the verdict components (`verdictComponent A R`: `accept(w)` may return `true` for
`w ∈ A`, `reject(w)` may return `false` for `w ∈ R`), the combined language is `A \ R`
(`strict_verdictComponent`). The cases:

* **accept only** (`w ∈ A`, `w ∉ R`): accepted (`accept_only`);
* **reject only** (`w ∉ A`, `w ∈ R`): rejected, not accepted (`reject_only`);
* **both, on different plays** (`w ∈ A ∩ R`): accepted by one play, rejected by another, so
  excluded (`both_runs`);
* **no outcomes** (`w ∉ A ∪ R`, or the bottom strategy): never rejected, vacuously, and not
  accepted (`no_outcome`, `bot_strict`);
* **divergence / no observation**: a call of `accept(w)` that is never answered is a play of
  every verdict component (`pending_call_mem`). It observes nothing, so it neither accepts nor
  rejects (`pending_only`).

**Refinement moves the combined language in neither direction**: adding a rejecting play
removes `w` (`not_mono_refinement`), and removing the accepting play removes `w`
(`not_anti_refinement`).

Proofs: `Silmaril.Proofs.Wasi.Component.Accept.Strict`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Examples

open Silmaril.Games Silmaril.Formats.Accept Silmaril.Wasi Silmaril.Wasi.Accept

/-- The combined language of the verdict component. -/
theorem not_mem_zero (w : List UInt8) : w ∉ (0 : ByteLang) := fun h => h

abbrev strict {I X : Set FnName} (σ : Strategy (nsig I) (nsig X)) : Set (List UInt8) :=
  exportAcceptedNotRejected σ acceptFn rejectExport (args1 bytes?)

theorem strict_verdictComponent (A R : ByteLang) :
    strict (verdictComponent A R) = (A : Set (List UInt8)) \ R :=
  Silmaril.Proofs.Wasi.Component.Accept.strict_verdictComponent A R

theorem accept_only {A R : ByteLang} {w : List UInt8} (ha : w ∈ A) (hr : w ∉ R) :
    w ∈ strict (verdictComponent A R) := by
  rw [strict_verdictComponent]; exact ⟨ha, hr⟩

theorem reject_only {A R : ByteLang} {w : List UInt8} (ha : w ∉ A) (hr : w ∈ R) :
    w ∉ strict (verdictComponent A R) ∧
      w ∈ exportRejected (verdictComponent A R) rejectExport (args1 bytes?) := by
  rw [strict_verdictComponent,
    Silmaril.Proofs.Wasi.Component.Accept.exportRejected_verdictComponent]
  exact ⟨fun h => ha h.1, hr⟩

/-- **Accepted by one play, rejected by another: excluded.** -/
theorem both_runs {A R : ByteLang} {w : List UInt8} (ha : w ∈ A) (hr : w ∈ R) :
    w ∈ exportBytesLang (verdictComponent A R) acceptFn ∧
      w ∉ strict (verdictComponent A R) := by
  rw [strict_verdictComponent,
    Silmaril.Proofs.Wasi.Component.Accept.exportBytesLang_verdictComponent]
  exact ⟨ha, fun h => h.2 hr⟩

/-- **No outcome**: never rejected, vacuously, but not accepted. -/
theorem no_outcome {A R : ByteLang} {w : List UInt8} (ha : w ∉ A) (hr : w ∉ R) :
    w ∈ neverFalse (verdictComponent A R) rejectExport (args1 bytes?) ∧
      w ∉ strict (verdictComponent A R) := by
  rw [strict_verdictComponent]
  refine ⟨?_, fun h => ha h.1⟩
  show w ∉ exportRejected _ _ _
  rw [Silmaril.Proofs.Wasi.Component.Accept.exportRejected_verdictComponent]; exact hr

/-- The bottom strategy (no answers at all) accepts nothing. -/
theorem bot_strict : strict (⊥ : Strategy (nsig ∅) (nsig verdictFns)) = ∅ := by
  rw [← Set.subset_empty_iff]
  intro w hw
  change w ∈ exportAcceptedNotRejected _ _ _ _ at hw
  rw [exportAcceptedNotRejected_eq_acceptsSafely] at hw
  obtain ⟨⟨e, ⟨⟨t, ⟨s, hs, rfl⟩, he⟩, -⟩, args, rfl⟩, -⟩ := hw
  rcases Strategy.mem_bot.1 hs with rfl | ⟨q, rfl⟩
  · simp [wtrace] at he
  · simp [wtrace, wev] at he

/-- **A pending call** (never answered: diverging, stuck or still running) is a play of every
verdict component, for every argument. -/
theorem pending_call_mem (A R : ByteLang) (w : List UInt8) :
    [.inr (.ask (⟨acceptFn, acceptFn_mem_verdictFns⟩, [bytesVal w]))] ∈
      (verdictComponent A R).plays :=
  (verdictComponent A R).receptive (s := []) (verdictComponent A R).nil_mem (.nil _) (.ask _)
    trivial

/-- ... and a value whose only plays are pending calls is neither accepted nor rejected. -/
theorem pending_only {w : List UInt8} :
    w ∉ strict (verdictComponent 0 0) ∧
      w ∈ neverFalse (verdictComponent 0 0) rejectExport (args1 bytes?) :=
  (no_outcome (A := 0) (R := 0) (not_mem_zero w) (not_mem_zero w)).symm

theorem verdictComponent_mono {A R A' R' : ByteLang} (hA : A ≤ A') (hR : R ≤ R') :
    verdictComponent A R ≤ verdictComponent A' R' :=
  Strategy.generate_mono fun _ hs => hs.elim
    (fun ⟨w, hw, h⟩ => .inl ⟨w, hA hw, h⟩) (fun ⟨w, hw, h⟩ => .inr ⟨w, hR hw, h⟩)

/-- **Not monotone**: a refining strategy can keep a value that the refined one rejects
(the larger strategy has an extra rejecting play). -/
theorem not_mono_refinement :
    ¬ ∀ σ τ : Strategy (nsig ∅) (nsig verdictFns), σ ≤ τ → strict σ ⊆ strict τ := by
  intro h
  have := h (verdictComponent {[]} 0) (verdictComponent {[]} {[]})
    (verdictComponent_mono le_rfl (fun _ h => (not_mem_zero _ h).elim))
    (accept_only (Set.mem_singleton _) (not_mem_zero _))
  rw [strict_verdictComponent] at this
  exact this.2 (Set.mem_singleton _)

/-- **Not antitone**: a refining strategy can lose the accepting witness. -/
theorem not_anti_refinement :
    ¬ ∀ σ τ : Strategy (nsig ∅) (nsig verdictFns), σ ≤ τ → strict τ ⊆ strict σ := by
  intro h
  have := h (verdictComponent 0 0) (verdictComponent {[]} 0)
    (verdictComponent_mono (fun _ h => (not_mem_zero _ h).elim) le_rfl)
    (accept_only (Set.mem_singleton _) (not_mem_zero _))
  rw [strict_verdictComponent] at this
  exact not_mem_zero _ this.1

end Silmaril.Wasi.Accept.Examples
