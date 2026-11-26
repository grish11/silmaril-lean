module

public import Silmaril.Semantics.Page.Examples.Defs
public import Silmaril.Semantics.Page.Thms

public section
namespace Silmaril.Semantics.Page.Examples.Proofs

private theorem completion_bit (bit : Bool) :
    Completion (singlePage Bool) (uninitialized Bool) (override (fun _ => none) 0 (some bit)) := by
  intro page
  change (override (empty Bool) 0 .undef page).CompletedBy (override (fun _ => none) 0 (some bit) page)
  by_cases eq : page = 0 <;> simp [override, eq, empty, Slot.CompletedBy]

private theorem pure_correctFrom {Content α : Type} (a : α) (m : MapMemory Nat Content)
    (i : Image Nat Content) {post : α → MapMemory Nat Content → Image Nat Content → Prop}
    (h : post a m i) : CorrectFrom (singlePage Content) (.pure a) m i post := by
  intro edits out run
  cases run
  refine ⟨⟨i, .nil⟩, ?_⟩
  intro final replay
  cases replay
  exact h

protected theorem initializeThenRead_correct :
    ForallCorrect (singlePage Bool) initializeThenRead (uninitialized Bool)
      (fun value final image => value = true ∧ final 0 = .defined true ∧ image 0 = some true) := by
  apply forallCorrect_of_correct
  intro edits out run
  change Run _ (.call (.write 0 true) (fun _ => Program.read 0)) _ _ _ at run
  cases run with
  | ub step => cases step with | writeAbsent absent => cases absent
  | call step readRun =>
    cases step with
    | write _ =>
      change Run _ (.call (.read 0) _) _ _ _ at readRun
      cases readRun with
      | ub step => cases step <;> rename_i impossible <;> cases impossible
      | call step done =>
        cases step with
        | readDefined lookup =>
          change Slot.defined true = Slot.defined _ at lookup
          cases lookup
          cases done
          intro image completion
          exact ⟨rfl, rfl, completion 0⟩

protected theorem forbidden_read :
    Run (singlePage Bool) (Program.read 0) (uninitialized Bool) [] (.stopped (.ub (.readUndef 0))) :=
  .ub (.readUndef rfl)

protected theorem forbidden_read_not_correct :
    ¬ ExistsCorrect (singlePage Bool) (Program.read 0) (uninitialized Bool) (fun _ _ _ => True) := by
  rintro ⟨_, _, all⟩
  exact all _ _ Proofs.forbidden_read

protected theorem allocation_exhausted :
    Run (singlePage Bool) Program.allocate (uninitialized Bool) [] (.returned none (uninitialized Bool)) := by
  have exhausted : ∀ page, ¬ (singlePage Bool).Fresh (uninitialized Bool) page := by
    intro page fresh
    have eq : page = 0 := fresh.2
    subst page
    cases fresh.1
  exact .call (.allocateNone exhausted) .pure

protected theorem deallocate_then_allocate :
    Run (singlePage Bool) ((Program.deallocate 0).bind fun _ => Program.allocate) (uninitialized Bool)
      [.deallocate 0, .allocate 0] (.returned (some 0) (uninitialized Bool)) := by
  let M := singlePage Bool
  let m := uninitialized Bool
  let removed := M.store.set m 0 .absent
  have fresh : M.Fresh removed 0 := ⟨rfl, rfl⟩
  have restore : M.store.set removed 0 .undef = m := by
    funext page
    change override (override m 0 .absent) 0 .undef page = override (empty Bool) 0 .undef page
    by_cases eq : page = 0 <;> simp [override, eq, m, uninitialized]
  apply run_bind_iff.mpr
  right
  refine ⟨(), removed, [.deallocate 0], [.allocate 0], rfl, ?_, ?_⟩
  · exact .call (.deallocate (by intro absent; cases absent)) .pure
  · have allocated : Run M Program.allocate removed [.allocate 0]
        (.returned (some 0) (M.store.set removed 0 .undef)) := .call (.allocate fresh) .pure
    rwa [restore] at allocated

protected theorem existential_bind_counterexample :
    ExistsCorrect (singlePage Bool) chooseBit (uninitialized Bool) (fun _ m _ => m = uninitialized Bool) ∧
    (∀ bit m, m = uninitialized Bool → ExistsCorrect (singlePage Bool) (.pure bit) m bitPost) ∧
    ¬ ExistsCorrect (singlePage Bool) (chooseBit.bind Program.pure) (uninitialized Bool) bitPost := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨_, completion_bit false, ?_⟩
    intro edits out run
    cases run with
    | left returned => cases returned; exact ⟨⟨_, .nil⟩, fun _ _ => rfl⟩
    | right returned => cases returned; exact ⟨⟨_, .nil⟩, fun _ _ => rfl⟩
  · rintro bit _ rfl
    exact ⟨_, completion_bit bit, pure_correctFrom bit _ _ rfl⟩
  · rintro ⟨image, _, all⟩
    have left : Run (singlePage Bool) (chooseBit.bind Program.pure) (uninitialized Bool) []
        (.returned false (uninitialized Bool)) := .left .pure
    have right : Run (singlePage Bool) (chooseBit.bind Program.pure) (uninitialized Bool) []
        (.returned true (uninitialized Bool)) := .right .pure
    have falseFill : image 0 = some false := (all _ _ left).2 image .nil
    have trueFill : image 0 = some true := (all _ _ right).2 image .nil
    simp [falseFill] at trueFill

protected theorem final_image_distinctions :
    ExistsCorrect (singlePage Bool) (.pure true) (uninitialized Bool) bitPost ∧
    ¬ ForallCorrect (singlePage Bool) (.pure true) (uninitialized Bool) bitPost ∧
    ForallCorrect (singlePage Bool) (.pure ()) (uninitialized Bool) (fun _ _ image => image 0 ≠ none) ∧
    ¬ Correct (singlePage Bool) (.pure ()) (uninitialized Bool)
      (fun _ m => definedImage (singlePage Bool) m 0 ≠ none) := by
  refine ⟨⟨_, completion_bit true, pure_correctFrom true _ _ rfl⟩, ?_, ?_, ?_⟩
  · intro all
    have bad : some false = some true := (all.2 _ (completion_bit false) _ _ .pure).2 _ .nil
    cases bad
  · refine ⟨⟨_, completion_bit true⟩, fun image completion => pure_correctFrom () _ image ?_⟩
    exact (completion_domain completion 0).mpr (by intro absent; cases absent)
  · intro ordinary
    exact (ordinary _ _ .pure) rfl

protected theorem empty_contents :
    ForallCorrect (singlePage PEmpty) (.pure ()) (empty PEmpty) (fun _ _ _ => True) ∧
    ¬ ForallCorrect (singlePage PEmpty) (.pure ()) (uninitialized PEmpty) (fun _ _ _ => True) ∧
    ¬ ForallCorrect (singlePage PEmpty) Program.allocate (empty PEmpty) (fun _ _ _ => True) := by
  have valid : Completion (singlePage PEmpty) (empty PEmpty) (fun _ => none) := fun _ => rfl
  refine ⟨⟨⟨_, valid⟩, fun i _ => pure_correctFrom () _ i trivial⟩, ?_, ?_⟩
  · rintro ⟨⟨i, completion⟩, _⟩
    obtain ⟨value, _⟩ := completion 0
    exact PEmpty.elim value
  · intro all
    have run : Run (singlePage PEmpty) Program.allocate (empty PEmpty) [.allocate 0]
        (.returned (some 0) (uninitialized PEmpty)) := .call (.allocate ⟨rfl, rfl⟩) .pure
    obtain ⟨i, replay⟩ := (all.2 _ valid _ _ run).1
    cases replay with
    | cons applied _ =>
      obtain ⟨value, _⟩ := applied
      exact PEmpty.elim value

end Silmaril.Semantics.Page.Examples.Proofs
