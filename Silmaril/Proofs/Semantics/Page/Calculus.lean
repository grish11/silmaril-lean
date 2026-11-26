module

public import Silmaril.Semantics.Page.Defs

public section
namespace Silmaril.Semantics.Page.Proofs

universe u v w a b

variable {Id : Type u} {Content : Type v} {Memory : Type w} {α : Type a} {β : Type b}
variable {M : Model Id Content Memory}
variable {m : Memory} {p : Program Id Content α} {k : α → Program Id Content β}
variable {edit : Edit Id Content} {edits before after : List (Edit Id Content)}
variable {image middle finalImage : Image Id Content}

protected theorem step_exists (op : Op Id Content) (m : Memory) : ∃ action, Step M op m action := by
  classical
  cases op with
  | read page =>
    cases lookup : M.store.lookup m page with
    | absent => exact ⟨_, .readAbsent lookup⟩
    | undef => exact ⟨_, .readUndef lookup⟩
    | defined _ => exact ⟨_, .readDefined lookup⟩
  | write page value =>
    by_cases absent : M.store.lookup m page = .absent
    · exact ⟨_, .writeAbsent absent⟩
    · exact ⟨_, .write absent⟩
  | allocate =>
    by_cases fresh : ∃ page, M.Fresh m page
    · obtain ⟨page, available⟩ := fresh
      exact ⟨_, .allocate available⟩
    · exact ⟨_, .allocateNone fun page available => fresh ⟨page, available⟩⟩
  | deallocate page =>
    by_cases absent : M.store.lookup m page = .absent
    · exact ⟨_, .deallocateAbsent absent⟩
    · exact ⟨_, .deallocate absent⟩

protected theorem run_exists (p : Program Id Content α) (m : Memory) :
    ∃ edits out, Run M p m edits out := by
  induction p generalizing m with
  | pure => exact ⟨_, _, .pure⟩
  | diverge => exact ⟨_, _, .diverge⟩
  | choose _ _ left _ =>
    obtain ⟨edits, out, run⟩ := left m
    exact ⟨edits, out, .left run⟩
  | call op _ ih =>
    obtain ⟨action, step⟩ := Proofs.step_exists (M := M) op m
    cases action with
    | ub => exact ⟨_, _, .ub step⟩
    | ok reply m' edit =>
      obtain ⟨edits, out, run⟩ := ih reply m'
      exact ⟨edit.toList ++ edits, out, .call step run⟩

protected theorem run_bind_iff {out : Exit Id Memory β} :
    Run M (p.bind k) m edits out ↔
      (∃ stop, out = .stopped stop ∧ Run M p m edits (.stopped stop)) ∨
      ∃ a mid before after, edits = before ++ after ∧
        Run M p m before (.returned a mid) ∧ Run M (k a) mid after out := by
  constructor
  · induction p generalizing m edits out with
    | pure a => exact fun run => .inr ⟨a, m, [], edits, rfl, .pure, run⟩
    | diverge =>
      intro run
      cases run
      exact .inl ⟨_, rfl, .diverge⟩
    | choose l r left right =>
      intro run
      cases run with
      | left run =>
        rcases left run with ⟨stop, rfl, prefixRun⟩ | ⟨a, mid, before, after, rfl, prefixRun, suffixRun⟩
        · exact .inl ⟨stop, rfl, .left prefixRun⟩
        · exact .inr ⟨a, mid, before, after, rfl, .left prefixRun, suffixRun⟩
      | right run =>
        rcases right run with ⟨stop, rfl, prefixRun⟩ | ⟨a, mid, before, after, rfl, prefixRun, suffixRun⟩
        · exact .inl ⟨stop, rfl, .right prefixRun⟩
        · exact .inr ⟨a, mid, before, after, rfl, .right prefixRun, suffixRun⟩
    | call op next ih =>
      intro run
      cases run with
      | ub step => exact .inl ⟨_, rfl, .ub step⟩
      | call step run =>
        rcases ih _ run with ⟨stop, rfl, prefixRun⟩ | ⟨a, mid, before, after, rfl, prefixRun, suffixRun⟩
        · exact .inl ⟨stop, rfl, .call step prefixRun⟩
        · exact .inr ⟨a, mid, _, after, (List.append_assoc ..).symm, .call step prefixRun, suffixRun⟩
  · rintro (⟨stop, rfl, run⟩ | ⟨a, mid, before, after, rfl, run, tail⟩)
    · generalize h : Exit.stopped stop = terminal at run
      induction run with
      | pure => cases h
      | diverge => cases h; exact .diverge
      | left _ ih => exact .left (ih h)
      | right _ ih => exact .right (ih h)
      | call step _ ih => exact .call step (ih h)
      | ub step => cases h; exact .ub step
    · generalize h : Exit.returned a mid = terminal at run
      induction run with
      | pure => cases h; exact tail
      | diverge => cases h
      | left _ ih => exact .left (ih h)
      | right _ ih => exact .right (ih h)
      | call step _ ih => rw [List.append_assoc]; exact .call step (ih h)
      | ub => cases h

protected theorem domain_set (store : Store Id Content Memory) (m : Memory) (p q : Id) (s : Slot Content) :
    store.domain (store.set m p s) q ↔
      (q = p ∧ s ≠ .absent) ∨ (q ≠ p ∧ store.domain m q) := by
  by_cases same : q = p
  · subst q
    simp [Store.domain, store.lookup_set_same]
  · simp [Store.domain, same, store.lookup_set_other _ _ _ _ same]

protected theorem exists_completion [Nonempty Content] (m : Memory) : ∃ image, Completion M m image := by
  obtain ⟨fallback⟩ := ‹Nonempty Content›
  refine ⟨fun p => match M.store.lookup m p with
    | .absent => none
    | .undef => some fallback
    | .defined value => some value, ?_⟩
  intro p
  cases lookup : M.store.lookup m p <;> simp [lookup, Slot.CompletedBy]

protected theorem completion_domain (h : Completion M m image) (page : Id) :
    image page ≠ none ↔ M.store.domain m page := by
  have fill := h page
  cases lookup : M.store.lookup m page with
  | absent => simp [Store.domain, lookup, Slot.CompletedBy] at fill ⊢; exact fill
  | defined value =>
    have eq : image page = some value := by simpa [lookup, Slot.CompletedBy] using fill
    simp [Store.domain, lookup, eq]
  | undef =>
    obtain ⟨value, eq⟩ : ∃ value, image page = some value := by simpa [lookup, Slot.CompletedBy] using fill
    simp [Store.domain, lookup, eq]

protected theorem completion_defined (h : FullyDefined M m) :
    Completion M m image ↔ image = definedImage M m := by
  constructor
  · intro completion
    funext page
    have fill := completion page
    cases lookup : M.store.lookup m page with
    | absent => simpa [definedImage, lookup, Slot.value, Slot.CompletedBy] using fill
    | defined value => simpa [definedImage, lookup, Slot.value, Slot.CompletedBy] using fill
    | undef => exact (h page lookup).elim
  · rintro rfl page
    cases lookup : M.store.lookup m page with
    | absent => simp [definedImage, lookup, Slot.value, Slot.CompletedBy]
    | defined value => simp [definedImage, lookup, Slot.value, Slot.CompletedBy]
    | undef => exact (h page lookup).elim

protected theorem completion_unique [Subsingleton Content] {other : Image Id Content}
    (first : Completion M m image) (second : Completion M m other) : image = other := by
  funext page
  have sameDomain := (Proofs.completion_domain first page).trans (Proofs.completion_domain second page).symm
  cases hi : image page <;> cases hj : other page
  · rfl
  · simp [hi, hj] at sameDomain
  · simp [hi, hj] at sameDomain
  · congr 1
    exact Subsingleton.elim _ _

protected theorem correct_bind {P : α → Memory → Prop} {Q : β → Memory → Prop}
    (first : Correct M p m P) (second : ∀ a mid, P a mid → Correct M (k a) mid Q) :
    Correct M (p.bind k) m Q := by
  intro edits out run
  rcases Proofs.run_bind_iff.mp run with ⟨stop, rfl, prefixRun⟩ | ⟨a, mid, _, after, _, prefixRun, suffixRun⟩
  · exact (first _ _ prefixRun).elim
  · exact second a mid (first _ _ prefixRun) after out suffixRun

section Replay
variable [DecidableEq Id]

protected theorem replay_exists [Nonempty Content] (edits : List (Edit Id Content)) (image : Image Id Content) :
    ∃ finalImage, Replay edits image finalImage := by
  induction edits generalizing image with
  | nil => exact ⟨image, .nil⟩
  | cons edit edits ih =>
    have extend : ∃ next, edit.Apply image next := by
      cases edit with
      | allocate page =>
        obtain ⟨value⟩ := ‹Nonempty Content›
        exact ⟨_, value, rfl⟩
      | write => exact ⟨_, rfl⟩
      | deallocate => exact ⟨_, rfl⟩
    obtain ⟨next, applied⟩ := extend
    obtain ⟨finalImage, suffixReplay⟩ := ih next
    exact ⟨finalImage, .cons applied suffixReplay⟩

protected theorem replay_append :
    Replay (before ++ after) image finalImage ↔
      ∃ middle, Replay before image middle ∧ Replay after middle finalImage := by
  induction before generalizing image with
  | nil =>
    constructor
    · exact fun h => ⟨image, .nil, h⟩
    · rintro ⟨middle, prefixReplay, suffixReplay⟩
      cases prefixReplay
      exact suffixReplay
  | cons edit before ih =>
    constructor
    · intro replay
      cases replay with
      | cons applied remainder =>
        obtain ⟨middle, prefixReplay, suffixReplay⟩ := ih.mp remainder
        exact ⟨middle, .cons applied prefixReplay, suffixReplay⟩
    · rintro ⟨middle, prefixReplay, suffixReplay⟩
      cases prefixReplay with
      | cons applied remainder => exact .cons applied (ih.mpr ⟨middle, remainder, suffixReplay⟩)

private theorem completion_set {page : Id} {slot : Slot Content} {value : Option Content}
    (h : Completion M m image) (fill : slot.CompletedBy value) :
    Completion M (M.store.set m page slot) (override image page value) := by
  intro q
  by_cases same : q = page
  · subst q
    simpa [M.store.lookup_set_same, override] using fill
  · simpa [M.store.lookup_set_other _ _ _ _ same, override, same] using h q

protected theorem step_completion {op : Op Id Content} {reply : Reply op} {m' : Memory}
    {edit : Option (Edit Id Content)} (step : Step M op m (.ok reply m' edit))
    (h : Completion M m image) (replay : Replay edit.toList image finalImage) :
    Completion M m' finalImage := by
  cases step with
  | readDefined _ => cases replay; exact h
  | allocateNone _ => cases replay; exact h
  | allocate _ =>
    cases replay with
    | cons applied rest =>
      cases rest
      obtain ⟨value, rfl⟩ := applied
      exact completion_set h ⟨value, rfl⟩
  | write _ =>
    cases replay with
    | cons applied rest =>
      cases rest
      cases applied
      exact completion_set h rfl
  | deallocate _ =>
    cases replay with
    | cons applied rest =>
      cases rest
      cases applied
      exact completion_set h rfl

protected theorem run_completion {a : α} {m' : Memory} (run : Run M p m edits (.returned a m'))
    (completion : Completion M m image) (replay : Replay edits image finalImage) :
    Completion M m' finalImage := by
  generalize h : Exit.returned a m' = terminal at run
  induction run generalizing image with
  | pure => cases h; cases replay; exact completion
  | diverge => cases h
  | left _ ih => exact ih completion replay h
  | right _ ih => exact ih completion replay h
  | ub => cases h
  | call step _ ih =>
    obtain ⟨middle, first, rest⟩ := Proofs.replay_append.mp replay
    exact ih (Proofs.step_completion step completion first) rest h

protected theorem correctFrom_bind {P : α → Memory → Image Id Content → Prop}
    {Q : β → Memory → Image Id Content → Prop}
    (first : CorrectFrom M p m image P)
    (second : ∀ a mid middle, P a mid middle → CorrectFrom M (k a) mid middle Q) :
    CorrectFrom M (p.bind k) m image Q := by
  intro edits out run
  rcases Proofs.run_bind_iff.mp run with ⟨stop, rfl, prefixRun⟩ | ⟨a, mid, before, after, rfl, prefixRun, suffixRun⟩
  · exact (first _ _ prefixRun).elim
  · obtain ⟨⟨middle, replay⟩, all⟩ := first before _ prefixRun
    have tail := second a mid middle (all middle replay) after out suffixRun
    cases out with
    | stopped stop => exact tail
    | returned value m' =>
      obtain ⟨⟨finalImage, suffixReplay⟩, _⟩ := tail
      refine ⟨⟨finalImage, Proofs.replay_append.mpr ⟨middle, replay, suffixReplay⟩⟩, ?_⟩
      intro finalImage combined
      obtain ⟨middle, prefixReplay, suffixReplay⟩ := Proofs.replay_append.mp combined
      exact (second a mid middle (all middle prefixReplay) after _ suffixRun).2 finalImage suffixReplay

protected theorem correct_lift_exists {Q : α → Memory → Image Id Content → Prop}
    (h : ExistsCorrect M p m Q) : Correct M p m (fun a m' => ∃ i, Completion M m' i ∧ Q a m' i) := by
  obtain ⟨image, completion, all⟩ := h
  intro edits out run
  cases out with
  | stopped => exact all _ _ run
  | returned a m' =>
    obtain ⟨⟨i, replay⟩, post⟩ := all _ _ run
    exact ⟨i, Proofs.run_completion run completion replay, post i replay⟩

protected theorem correctFrom_of_correct [Nonempty Content] {Q : α → Memory → Image Id Content → Prop}
    (h : Correct M p m (fun a m' => ∀ i, Completion M m' i → Q a m' i))
    (completion : Completion M m image) : CorrectFrom M p m image Q := by
  intro edits out run
  cases out with
  | stopped => exact h _ _ run
  | returned a m' =>
    exact ⟨Proofs.replay_exists edits image, fun i replay => h _ _ run i (Proofs.run_completion run completion replay)⟩

variable {P : α → Memory → Image Id Content → Prop} {Q : β → Memory → Image Id Content → Prop}

private theorem correctFrom_bind_of_completion (initial : Completion M m image)
    (first : CorrectFrom M p m image P)
    (second : ∀ a mid middle, Completion M mid middle → P a mid middle → CorrectFrom M (k a) mid middle Q) :
    CorrectFrom M (p.bind k) m image Q := by
  refine Proofs.correctFrom_bind (P := fun a mid middle => Completion M mid middle ∧ P a mid middle) ?_ ?_
  · intro edits out run
    have verified := first edits out run
    cases out with
    | stopped => exact verified
    | returned value m' =>
      exact ⟨verified.1, fun middle replay => ⟨Proofs.run_completion run initial replay, verified.2 middle replay⟩⟩
  · exact fun a mid middle h => second a mid middle h.1 h.2

protected theorem existsCorrect_bind (first : ExistsCorrect M p m P)
    (second : ∀ a mid middle, Completion M mid middle → P a mid middle → CorrectFrom M (k a) mid middle Q) :
    ExistsCorrect M (p.bind k) m Q := by
  obtain ⟨image, valid, verified⟩ := first
  exact ⟨image, valid, correctFrom_bind_of_completion valid verified second⟩

protected theorem forallCorrect_bind (first : ForallCorrect M p m P)
    (second : ∀ a mid, (∃ middle, Completion M mid middle ∧ P a mid middle) → ForallCorrect M (k a) mid Q) :
    ForallCorrect M (p.bind k) m Q := by
  refine ⟨first.1, fun image valid => correctFrom_bind_of_completion valid (first.2 image valid) ?_⟩
  exact fun a mid middle completed post => (second a mid ⟨middle, completed, post⟩).2 middle completed

protected theorem forallCorrect_of_existsCorrect_subsingleton [Subsingleton Content]
    (h : ExistsCorrect M p m P) : ForallCorrect M p m P := by
  obtain ⟨image, valid, run⟩ := h
  refine ⟨⟨image, valid⟩, fun other completed => ?_⟩
  rwa [Proofs.completion_unique completed valid]

protected theorem correct_iff_completion_on [Nonempty Content] {post : α → Memory → Prop}
    (agree : ∀ a m' edits i, Run M p m edits (.returned a m') → Completion M m' i →
      (P a m' i ↔ post a m')) :
    (Correct M p m post ↔ ExistsCorrect M p m P) ∧ (Correct M p m post ↔ ForallCorrect M p m P) := by
  have toAll (h : Correct M p m post) : ForallCorrect M p m P := by
    refine ⟨Proofs.exists_completion m, fun _ valid => Proofs.correctFrom_of_correct ?_ valid⟩
    intro edits out run
    cases out with
    | stopped => exact h edits _ run
    | returned a m' => exact fun i completed => (agree a m' edits i run completed).mpr (h edits _ run)
  have toExists (h : ForallCorrect M p m P) : ExistsCorrect M p m P := by
    obtain ⟨⟨image, valid⟩, all⟩ := h
    exact ⟨image, valid, all image valid⟩
  have toOrdinary (h : ExistsCorrect M p m P) : Correct M p m post := by
    intro edits out run
    have projected := Proofs.correct_lift_exists h edits out run
    cases out with
    | stopped => exact projected
    | returned a m' =>
      obtain ⟨i, valid, result⟩ := projected
      exact (agree a m' edits i run valid).mp result
  exact ⟨⟨fun h => toExists (toAll h), toOrdinary⟩, ⟨toAll, fun h => toOrdinary (toExists h)⟩⟩

protected theorem completion_correct_iff_fullyDefined (h : FullyDefined M m) :
    (ExistsCorrect M p m P ↔ CorrectFrom M p m (definedImage M m) P) ∧
    (ForallCorrect M p m P ↔ CorrectFrom M p m (definedImage M m) P) := by
  have valid : Completion M m (definedImage M m) := (Proofs.completion_defined h).mpr rfl
  constructor
  · constructor
    · rintro ⟨image, completion, run⟩
      rwa [(Proofs.completion_defined h).mp completion] at run
    · exact fun run => ⟨_, valid, run⟩
  · constructor
    · exact fun all => all.2 _ valid
    · exact fun run => ⟨⟨_, valid⟩, fun i completion => (Proofs.completion_defined h).mp completion ▸ run⟩

protected theorem correct_iff_completion_of_defined_returns [Nonempty Content]
    (defined : ∀ a m' edits, Run M p m edits (.returned a m') → FullyDefined M m') :
    (Correct M p m (fun a m' => P a m' (definedImage M m')) ↔ ExistsCorrect M p m P) ∧
    (Correct M p m (fun a m' => P a m' (definedImage M m')) ↔ ForallCorrect M p m P) := by
  apply Proofs.correct_iff_completion_on
  intro a m' edits i run completion
  rw [(Proofs.completion_defined (defined a m' edits run)).mp completion]

end Replay
end Silmaril.Semantics.Page.Proofs
