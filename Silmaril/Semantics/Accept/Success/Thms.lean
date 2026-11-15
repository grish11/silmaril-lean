module

public import Silmaril.Semantics.Accept.Success.Defs
public import Silmaril.Semantics.Accept.Rel.Thms

/-!
# Successful-value projections: laws

* membership: `mem_succ`, and for the extractors `mem_someVals` (`(a, some b) ∈ R`),
  `mem_okVals` (`.ok b`), `mem_errVals`, `mem_inlVals` (`inl b`), `mem_inrVals`;
* failures are dropped: `not_mem_dom_succ` (an input whose outputs all fail has no
  successful value) and `mem_dom_succ`;
* functoriality: `succ_comp` (Kleisli composition of extractors), `succ_some` (the trivial
  extractor), `succ_mono`, `succ_union`, `succ_empty`;
* partial functions and total maps: `succ_ofPartial`, `succ_ofTotal`;
* pullbacks: `pullSome_succ`, `pullAll_succ`;
* single-valuedness is preserved: `succ_single`.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w x y

open scoped SetRel

variable {α : Type u} {β : Type v} {γ : Type w} {ε : Type x} {δ : Type y}

/-! ## Extractors -/

@[simp] theorem optionOk_eq_some {o : Option β} {b : β} : optionOk o = some b ↔ o = some b :=
  Iff.rfl

@[simp] theorem exceptOk_ok (b : β) : exceptOk (.ok b : Except ε β) = some b := rfl
@[simp] theorem exceptOk_error (e : ε) : exceptOk (.error e : Except ε β) = none := rfl
@[simp] theorem exceptErr_ok (b : β) : exceptErr (.ok b : Except ε β) = none := rfl
@[simp] theorem exceptErr_error (e : ε) : exceptErr (.error e : Except ε β) = some e := rfl
@[simp] theorem sumOk_inl (b : β) : sumOk (.inl b : β ⊕ ε) = some b := rfl
@[simp] theorem sumOk_inr (e : ε) : sumOk (.inr e : β ⊕ ε) = none := rfl
@[simp] theorem sumErr_inl (b : β) : sumErr (.inl b : β ⊕ ε) = none := rfl
@[simp] theorem sumErr_inr (e : ε) : sumErr (.inr e : β ⊕ ε) = some e := rfl

@[simp] theorem exceptOk_eq_some {c : Except ε β} {b : β} : exceptOk c = some b ↔ c = .ok b := by
  cases c <;> simp [exceptOk]

@[simp] theorem exceptErr_eq_some {c : Except ε β} {e : ε} :
    exceptErr c = some e ↔ c = .error e := by cases c <;> simp [exceptErr]

@[simp] theorem sumOk_eq_some {c : β ⊕ ε} {b : β} : sumOk c = some b ↔ c = .inl b := by
  cases c <;> simp [sumOk]

@[simp] theorem sumErr_eq_some {c : β ⊕ ε} {e : ε} : sumErr c = some e ↔ c = .inr e := by
  cases c <;> simp [sumErr]

/-- `sumOk` is Mathlib's `Sum.getLeft?`. -/
theorem sumOk_eq_getLeft? : (sumOk : β ⊕ ε → Option β) = Sum.getLeft? := by
  funext c; cases c <;> rfl

/-- `exceptOk` is core's `Except.toOption`. -/
theorem exceptOk_eq_toOption : (exceptOk : Except ε β → Option β) = Except.toOption := by
  funext c; cases c <;> rfl

/-! ## Membership -/

section Mem

variable {f : γ → Option β} {R R' : α -|> γ} {a : α} {b : β}

theorem mem_succ : (a, b) ∈ succ f R ↔ ∃ c, (a, c) ∈ R ∧ f c = some b := Iff.rfl

@[simp] theorem mem_someVals {R : α -|> Option β} : (a, b) ∈ someVals R ↔ (a, some b) ∈ R := by
  simp [mem_succ]

@[simp] theorem mem_okVals {R : α -|> Except ε β} : (a, b) ∈ okVals R ↔ (a, .ok b) ∈ R := by
  simp [mem_succ]

@[simp] theorem mem_errVals {R : α -|> Except ε β} {e : ε} :
    (a, e) ∈ errVals R ↔ (a, .error e) ∈ R := by simp [mem_succ]

@[simp] theorem mem_inlVals {R : α -|> β ⊕ ε} : (a, b) ∈ inlVals R ↔ (a, .inl b) ∈ R := by
  simp [mem_succ]

@[simp] theorem mem_inrVals {R : α -|> β ⊕ ε} {e : ε} : (a, e) ∈ inrVals R ↔ (a, .inr e) ∈ R := by
  simp [mem_succ]

/-- An input has a successful value iff some output is a success. -/
theorem mem_dom_succ : a ∈ (succ f R).dom ↔ ∃ c, (a, c) ∈ R ∧ (f c).isSome := by
  simp [mem_succ, Option.isSome_iff_exists]; grind

/-- Failures are dropped: an input whose outputs all fail has no successful value. -/
theorem not_mem_dom_succ (h : ∀ c, (a, c) ∈ R → f c = none) : a ∉ (succ f R).dom :=
  fun ⟨_, c, hc, hf⟩ => by simp [h c hc] at hf

/-- `none` outputs are dropped by `someVals`. -/
theorem not_mem_dom_someVals {R : α -|> Option β} (h : ∀ c, (a, c) ∈ R → c = none) :
    a ∉ (someVals R).dom := not_mem_dom_succ fun c hc => by simp [optionOk, h c hc]

/-- `.error` outputs are dropped by `okVals`. -/
theorem not_mem_dom_okVals {R : α -|> Except ε β} (h : ∀ c, (a, c) ∈ R → ∃ e, c = .error e) :
    a ∉ (okVals R).dom := not_mem_dom_succ fun c hc => by obtain ⟨e, rfl⟩ := h c hc; rfl

/-- `inr` outputs are dropped by `inlVals`. -/
theorem not_mem_dom_inlVals {R : α -|> β ⊕ ε} (h : ∀ c, (a, c) ∈ R → ∃ e, c = .inr e) :
    a ∉ (inlVals R).dom := not_mem_dom_succ fun c hc => by obtain ⟨e, rfl⟩ := h c hc; rfl

end Mem

/-! ## Functoriality -/

section Functor

variable {f : γ → Option β} {R R' : α -|> γ}

/-- Projecting twice is projecting along the Kleisli composite of the extractors. -/
theorem succ_comp {g : β → Option δ} : succ g (succ f R) = succ (partialComp f g) R := by
  rw [succ, succ, succ, SetRel.comp_assoc, ofPartial_partialComp]

/-- The trivial extractor `some` keeps every output. -/
@[simp] theorem succ_some : succ some R = R := by ext ⟨a, c⟩; simp [mem_succ]

theorem succ_mono (h : R ⊆ R') : succ f R ⊆ succ f R' := SetRel.comp_subset_comp_left h

theorem succ_union : succ f (R ∪ R') = succ f R ∪ succ f R' := by
  ext ⟨a, b⟩; simp only [Set.mem_union, mem_succ]; grind

@[simp] theorem succ_empty : succ f (∅ : α -|> γ) = ∅ := SetRel.empty_comp _

theorem succ_ofPartial {g : α → Option γ} : succ f (ofPartial g) = ofPartial (partialComp g f) :=
  ofPartial_partialComp.symm

theorem succ_ofTotal {g : α → γ} : succ f (ofTotal g) = ofPartial (f ∘ g) := by
  ext ⟨a, b⟩; simp [mem_succ]

end Functor

/-! ## Pullbacks -/

section Pull

variable {f : γ → Option β} {R : α -|> γ} {L : Set β}

/-- Some successful value in `L` is some output whose success is in `L`. -/
theorem pullSome_succ : pullSome (succ f R) L = pullSome R {c | ∃ b ∈ L, f c = some b} := by
  rw [succ, pullSome_comp]; rfl

/-- Every successful value in `L` is every output being a failure or a success in `L`. -/
theorem pullAll_succ : pullAll (succ f R) L = pullAll R {c | ∀ b, f c = some b → b ∈ L} := by
  rw [succ, pullAll_comp]; rfl

end Pull

/-- Projection preserves single-valuedness (stated directly, with no functional-relation API). -/
theorem succ_single {f : γ → Option β} {R : α -|> γ}
    (hR : ∀ a c c', (a, c) ∈ R → (a, c') ∈ R → c = c') :
    ∀ a b b', (a, b) ∈ succ f R → (a, b') ∈ succ f R → b = b' :=
  fun a _ _ ⟨c, hc, hb⟩ ⟨c', hc', hb'⟩ => Option.some.inj (hb.symm.trans (hR a c c' hc hc' ▸ hb'))

end Silmaril.Accept
