module

public import Silmaril.Semantics.Brookes.Defs
import Silmaril.Proofs.Semantics.Brookes.Closure
import Silmaril.Proofs.Semantics.Brookes.Bind

public section

namespace Silmaril.Proofs.Semantics.Brookes

open Silmaril.Semantics.Brookes

universe u

variable {Store Step : Type u}

theorem shuffle_comm {left right merged : List Step}
    (merge : Shuffle left right merged) : Shuffle right left merged := by
  induction merge with
  | nil => exact .nil
  | left step _ ih => exact .right step ih
  | right step _ ih => exact .left step ih

private theorem shuffle_nonempty_left {left right merged : List Step}
    (merge : Shuffle left right merged) (hne : left ≠ []) : merged ≠ [] := by
  rintro rfl
  cases merge
  exact hne rfl

private theorem shuffle_prepend_left {left right merged : List Step}
    (merge : Shuffle left right merged) (steps : List Step) :
    Shuffle (steps ++ left) right (steps ++ merged) := by
  induction steps with
  | nil => exact merge
  | cons step _ ih => exact .left step ih

theorem shuffle_append (left right : List Step) : Shuffle left right (left ++ right) := by
  have fromRight : Shuffle [] right right := by
    induction right with
    | nil => exact .nil
    | cons step _ ih => exact .right step ih
  simpa only [List.append_nil] using shuffle_prepend_left fromRight left

private theorem shuffle_replace_left {left right merged : List Step}
    (merge : Shuffle left right merged) {pre post : List Step} {step : Step}
    (split : left = pre ++ step :: post) (replacement : List Step) :
    ∃ outPre outPost, merged = outPre ++ step :: outPost ∧
      Shuffle (pre ++ replacement ++ post) right (outPre ++ replacement ++ outPost) := by
  induction merge generalizing pre with
  | nil =>
    cases pre <;> simp at split
  | left head _ ih =>
    cases pre with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj split
      exact ⟨[], _, rfl, shuffle_prepend_left ‹Shuffle _ _ _› replacement⟩
    | cons item rest =>
      obtain ⟨hHead, eq⟩ := List.cons.inj split
      subst item
      obtain ⟨outPre, outPost, hEq, hShuffle⟩ := ih eq
      exact ⟨head :: outPre, outPost, congrArg (head :: ·) hEq, .left head hShuffle⟩
  | right head _ ih =>
    obtain ⟨outPre, outPost, hEq, hShuffle⟩ := ih split
    exact ⟨head :: outPre, outPost, congrArg (head :: ·) hEq, .right head hShuffle⟩

private theorem shuffle_of_rewrite_left {left left' right merged : Trace Store}
    (step : Rewrite left left') (merge : Shuffle left' right merged) :
    ∃ raw, Shuffle left right raw ∧ Rewrite raw merged := by
  cases step with
  | stutter pre post s =>
    obtain ⟨outPre, outPost, rfl, h⟩ := shuffle_replace_left merge rfl []
    simp only [List.append_nil] at h
    exact ⟨_, h, Rewrite.stutter outPre outPost s⟩
  | mumble pre post s t u =>
    obtain ⟨outPre, outPost, rfl, h⟩ := shuffle_replace_left merge rfl [(s, t), (t, u)]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    exact ⟨_, h, Rewrite.mumble outPre outPost s t u⟩

/-- A deduction before a shuffle can be delayed until after the shuffle. -/
theorem shuffle_of_reduces_left {left left' right merged : Trace Store}
    (deduction : Reduces left left') (merge : Shuffle left' right merged) :
    ∃ raw, Shuffle left right raw ∧ Reduces raw merged := by
  induction deduction generalizing merged with
  | refl => exact ⟨_, merge, .refl _⟩
  | tail _ step ih =>
    obtain ⟨intermediate, hShuffle, hRewrite⟩ := shuffle_of_rewrite_left step merge
    obtain ⟨raw, hRaw, hReduces⟩ := ih hShuffle
    exact ⟨raw, hRaw, hReduces.tail hRewrite⟩

theorem parallel_accepts_iff {first second : Command Store} {trace : Trace Store} :
    (Command.parallel first second).accepts trace () ↔
      ∃ left right merged, first.accepts left () ∧ second.accepts right () ∧
        Shuffle left right merged ∧ Reduces merged trace := by
  constructor
  · rintro ⟨merged, ⟨_, left, right, hl, hr, hs⟩, hd⟩
    exact ⟨left, right, merged, hl, hr, hs, hd⟩
  · rintro ⟨left, right, merged, hl, hr, hs, hd⟩
    exact ⟨merged, ⟨shuffle_nonempty_left hs (first.nonempty hl), left, right, hl, hr, hs⟩, hd⟩

theorem parallel_generate (leftSeed rightSeed : Trace Store → Unit → Prop) :
    Command.parallel (Behavior.generate leftSeed) (Behavior.generate rightSeed) =
      Behavior.generate (fun word _ =>
        ∃ left right, left ≠ [] ∧ right ≠ [] ∧ leftSeed left () ∧ rightSeed right () ∧
          Shuffle left right word) := by
  apply behavior_ext
  intro trace result
  cases result
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨_, _, merged, ⟨left, ⟨hlne, hl⟩, hleft⟩, ⟨right, ⟨hrne, hr⟩, hright⟩, hs, hd⟩
    obtain ⟨afterLeft, hLeft, dLeft⟩ := shuffle_of_reduces_left hleft hs
    obtain ⟨raw, hRaw, dRight⟩ := shuffle_of_reduces_left hright (shuffle_comm hLeft)
    exact ⟨raw, ⟨shuffle_nonempty_left hRaw hrne, left, right, hlne, hrne, hl, hr, shuffle_comm hRaw⟩,
      Reduces.trans dRight (Reduces.trans dLeft hd)⟩
  · rintro ⟨raw, ⟨_, left, right, hlne, hrne, hl, hr, hs⟩, hd⟩
    exact ⟨left, right, raw, generate_accepts hlne hl, generate_accepts hrne hr, hs, hd⟩

theorem parallel_comm (first second : Command Store) :
    Command.parallel first second = Command.parallel second first := by
  apply behavior_ext
  intro trace result
  cases result
  simp only [parallel_accepts_iff]
  constructor <;> rintro ⟨left, right, merged, hl, hr, hs, hd⟩ <;>
    exact ⟨right, left, merged, hr, hl, shuffle_comm hs, hd⟩

theorem seq_le_parallel {first second : Command Store} {trace : Trace Store}
    (h : (Command.seq first second).accepts trace ()) :
    (Command.parallel first second).accepts trace () := by
  obtain ⟨left, right, _, hl, hr, hd⟩ := bind_accepts_iff.mp h
  exact parallel_accepts_iff.mpr ⟨left, right, _, hl, hr, shuffle_append left right, hd⟩

theorem parallel_completes_iff {first second : Command Store} {s t : Store} :
    (Command.parallel first second).completes s t () ↔
      ∃ left right merged, first.accepts left () ∧ second.accepts right () ∧
        Shuffle left right merged ∧ Runs s merged t := by
  constructor
  · intro h
    obtain ⟨left, right, merged, hl, hr, hs, hd⟩ := parallel_accepts_iff.mp h
    exact ⟨left, right, merged, hl, hr, hs, runs_of_reduces hd (.cons (.nil t))⟩
  · rintro ⟨left, right, merged, hl, hr, hs, run⟩
    have h := parallel_accepts_iff.mpr ⟨left, right, merged, hl, hr, hs, .refl _⟩
    exact (Command.parallel first second).stable h
      (reduces_singleton_of_runs run ((Command.parallel first second).nonempty h))

private theorem shuffle_nil_left {right merged : List Step}
    (h : Shuffle [] right merged) : merged = right := by
  generalize he : ([] : List Step) = left at h
  induction h with
  | nil => rfl
  | left _ _ _ => contradiction
  | right step _ ih => exact congrArg (step :: ·) (ih he)

theorem parallel_skip_left (command : Command Store) :
    Command.parallel Command.skip command = command := by
  apply behavior_ext
  intro trace result
  cases result
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨left, right, merged, hl, hr, hs, hd⟩
    obtain ⟨s, _, hRet⟩ := ret_accepts_iff.mp hl
    obtain ⟨raw, hRaw, hReduced⟩ := shuffle_of_reduces_left hRet hs
    obtain ⟨pre, post, rfl, hRemoved⟩ :=
      shuffle_replace_left hRaw (pre := []) (post := []) (step := (s, s)) rfl []
    have hEq : pre ++ post = right := by
      simpa only [List.append_nil] using shuffle_nil_left hRemoved
    have insert := Reduces.tail (.refl _) (Rewrite.stutter pre post s)
    exact command.stable (hEq ▸ hr : command.accepts (pre ++ post) ())
      (Reduces.trans insert (Reduces.trans hReduced hd))
  · intro h
    have hne := command.nonempty h
    cases trace with
    | nil => exact False.elim (hne rfl)
    | cons step rest =>
      rcases step with ⟨s, t⟩
      exact ⟨[(s, s)], _, _, ret_accepts_iff.mpr ⟨s, rfl, .refl _⟩, h,
        shuffle_append [(s, s)] ((s, t) :: rest),
        .tail (.refl _) (Rewrite.mumble [] rest s s t)⟩

end Silmaril.Proofs.Semantics.Brookes
