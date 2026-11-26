module

public import Silmaril.Semantics.Page.Defs
import Silmaril.Proofs.Semantics.Page.Calculus

public section
namespace Silmaril.Semantics.Page

universe u v w a b

variable {Id : Type u} {Content : Type v} {Memory : Type w} {α : Type a} {β : Type b}
variable {M : Model Id Content Memory} {m : Memory} {p : Program Id Content α}
variable {k : α → Program Id Content β}
variable {edits before after : List (Edit Id Content)}
variable {image finalImage : Image Id Content}

theorem step_exists (op : Op Id Content) (m : Memory) : ∃ action, Step M op m action :=
  Proofs.step_exists op m

theorem run_exists (p : Program Id Content α) (m : Memory) : ∃ edits out, Run M p m edits out :=
  Proofs.run_exists p m

theorem run_bind_iff {out : Exit Id Memory β} :
    Run M (p.bind k) m edits out ↔
      (∃ stop, out = .stopped stop ∧ Run M p m edits (.stopped stop)) ∨
      ∃ a mid before after, edits = before ++ after ∧
        Run M p m before (.returned a mid) ∧ Run M (k a) mid after out :=
  Proofs.run_bind_iff

theorem domain_set (store : Store Id Content Memory) (m : Memory) (p q : Id) (s : Slot Content) :
    store.domain (store.set m p s) q ↔
      (q = p ∧ s ≠ .absent) ∨ (q ≠ p ∧ store.domain m q) :=
  Proofs.domain_set store m p q s

theorem allocate_some_iff {page : Id} {target : Memory} {edit : Option (Edit Id Content)} :
    Step M .allocate m (.ok (.allocated (some page)) target edit) ↔
      M.Fresh m page ∧ target = M.store.set m page .undef ∧ edit = some (.allocate page) := by
  constructor
  · intro step; cases step with | allocate fresh => exact ⟨fresh, rfl, rfl⟩
  · rintro ⟨fresh, rfl, rfl⟩; exact .allocate fresh

theorem allocate_none_iff {target : Memory} {edit : Option (Edit Id Content)} :
    Step M .allocate m (.ok (.allocated none) target edit) ↔
      (∀ page, ¬ M.Fresh m page) ∧ target = m ∧ edit = none := by
  constructor
  · intro step; cases step with | allocateNone exhausted => exact ⟨exhausted, rfl, rfl⟩
  · rintro ⟨exhausted, rfl, rfl⟩; exact .allocateNone exhausted

theorem exists_completion [Nonempty Content] (m : Memory) : ∃ image, Completion M m image :=
  Proofs.exists_completion m

theorem completion_domain (h : Completion M m image) (page : Id) :
    image page ≠ none ↔ M.store.domain m page :=
  Proofs.completion_domain h page

theorem completion_defined (h : FullyDefined M m) :
    Completion M m image ↔ image = definedImage M m :=
  Proofs.completion_defined h

theorem completion_unique [Subsingleton Content] {other : Image Id Content}
    (first : Completion M m image) (second : Completion M m other) : image = other :=
  Proofs.completion_unique first second

theorem correct_bind {P : α → Memory → Prop} {Q : β → Memory → Prop}
    (first : Correct M p m P) (second : ∀ a mid, P a mid → Correct M (k a) mid Q) :
    Correct M (p.bind k) m Q :=
  Proofs.correct_bind first second

section Completion
variable [DecidableEq Id]
variable {P : α → Memory → Image Id Content → Prop} {Q : β → Memory → Image Id Content → Prop}

theorem replay_exists [Nonempty Content] (edits : List (Edit Id Content)) (image : Image Id Content) :
    ∃ finalImage, Replay edits image finalImage :=
  Proofs.replay_exists edits image

theorem replay_append :
    Replay (before ++ after) image finalImage ↔
      ∃ middle, Replay before image middle ∧ Replay after middle finalImage :=
  Proofs.replay_append

theorem step_completion {op : Op Id Content} {reply : Reply op} {m' : Memory}
    {edit : Option (Edit Id Content)} (step : Step M op m (.ok reply m' edit))
    (h : Completion M m image) (replay : Replay edit.toList image finalImage) :
    Completion M m' finalImage :=
  Proofs.step_completion step h replay

theorem run_completion {value : α} {m' : Memory} (run : Run M p m edits (.returned value m'))
    (completion : Completion M m image) (replay : Replay edits image finalImage) :
    Completion M m' finalImage :=
  Proofs.run_completion run completion replay

theorem correctFrom_bind (first : CorrectFrom M p m image P)
    (second : ∀ a mid middle, P a mid middle → CorrectFrom M (k a) mid middle Q) :
    CorrectFrom M (p.bind k) m image Q :=
  Proofs.correctFrom_bind first second

/-- Existential sequencing works when the suffix accepts the actual image
left by every prefix execution and replay. -/
theorem existsCorrect_bind (first : ExistsCorrect M p m P)
    (second : ∀ a mid middle, Completion M mid middle → P a mid middle → CorrectFrom M (k a) mid middle Q) :
    ExistsCorrect M (p.bind k) m Q :=
  Proofs.existsCorrect_bind first second

theorem forallCorrect_bind (first : ForallCorrect M p m P)
    (second : ∀ a mid, (∃ middle, Completion M mid middle ∧ P a mid middle) → ForallCorrect M (k a) mid Q) :
    ForallCorrect M (p.bind k) m Q :=
  Proofs.forallCorrect_bind first second

theorem existsCorrect_of_forallCorrect (h : ForallCorrect M p m P) : ExistsCorrect M p m P := by
  obtain ⟨⟨image, valid⟩, all⟩ := h
  exact ⟨image, valid, all image valid⟩

theorem forallCorrect_of_existsCorrect_subsingleton [Subsingleton Content]
    (h : ExistsCorrect M p m P) : ForallCorrect M p m P :=
  Proofs.forallCorrect_of_existsCorrect_subsingleton h

theorem correct_of_existsCorrect (h : ExistsCorrect M p m P) :
    Correct M p m (fun a m' => ∃ i, Completion M m' i ∧ P a m' i) :=
  Proofs.correct_lift_exists h

theorem forallCorrect_of_correct [Nonempty Content]
    (h : Correct M p m (fun a m' => ∀ i, Completion M m' i → P a m' i)) : ForallCorrect M p m P :=
  ⟨exists_completion m, fun _ valid => Proofs.correctFrom_of_correct h valid⟩

theorem correct_iff_completion_on [Nonempty Content] {post : α → Memory → Prop}
    (agree : ∀ a m' edits i, Run M p m edits (.returned a m') → Completion M m' i →
      (P a m' i ↔ post a m')) :
    (Correct M p m post ↔ ExistsCorrect M p m P) ∧ (Correct M p m post ↔ ForallCorrect M p m P) :=
  Proofs.correct_iff_completion_on agree

/-- If the postcondition ignores the completed image, completion quantification
has no effect on total correctness when contents are inhabited. -/
theorem correct_iff_completion [Nonempty Content] (post : α → Memory → Prop) :
    (Correct M p m post ↔ ExistsCorrect M p m (fun a m' _ => post a m')) ∧
    (Correct M p m post ↔ ForallCorrect M p m (fun a m' _ => post a m')) :=
  correct_iff_completion_on (fun _ _ _ _ _ _ => Iff.rfl)

/-- Fully defined inputs have one possible initial image, even for empty contents. -/
theorem completion_correct_iff_fullyDefined (h : FullyDefined M m) :
    (ExistsCorrect M p m P ↔ CorrectFrom M p m (definedImage M m) P) ∧
    (ForallCorrect M p m P ↔ CorrectFrom M p m (definedImage M m) P) :=
  Proofs.completion_correct_iff_fullyDefined h

/-- When every normal final memory is fully defined, all three readings agree on
postconditions that inspect the completed final image. -/
theorem correct_iff_completion_of_defined_returns [Nonempty Content]
    (defined : ∀ a m' edits, Run M p m edits (.returned a m') → FullyDefined M m') :
    (Correct M p m (fun a m' => P a m' (definedImage M m')) ↔ ExistsCorrect M p m P) ∧
    (Correct M p m (fun a m' => P a m' (definedImage M m')) ↔ ForallCorrect M p m P) :=
  Proofs.correct_iff_completion_of_defined_returns defined

end Completion
end Silmaril.Semantics.Page
