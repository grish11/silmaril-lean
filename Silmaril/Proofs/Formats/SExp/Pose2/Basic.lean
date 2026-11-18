module

public import Silmaril.Formats.SExp.Pose2.Defs

/-! # Proofs: POSE data are the proper `Pose2` values with POSE text -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Pose2

open Silmaril.Formats

variable {α : Type}

theorem toSExp2_ofList (l : List (SExp α)) :
    (SExp.ofList l).toSExp2 = SExp2.ofList (l.map SExp.toSExp2) := by
  change SExp2.ofList (List.ofFn fun i => SExp.toSExp2 l[i]) = _
  exact congrArg SExp2.ofList (List.ofFn_getElem_eq_map l SExp.toSExp2)

theorem toProper_sound : ∀ n : Nat,
    (∀ (e : SExp2 α) p, SExpParser.toProper n e = some p → p.toSExp2 = e) ∧
    (∀ (e : SExp2 α) ps, SExpParser.toProperList n e = some ps →
      SExp2.ofList (ps.map SExp.toSExp2) = e) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => by simp [SExpParser.toProper] at h,
      fun _ _ h => by simp [SExpParser.toProperList] at h⟩
  | succ n ih =>
      refine ⟨fun e p h => ?_, fun e ps h => ?_⟩
      · cases e with
        | nil =>
            simp only [SExpParser.toProper, Option.some.injEq] at h; subst h
            rfl
        | atom a => simp only [SExpParser.toProper, Option.some.injEq] at h; subst h; rfl
        | cons a d =>
            simp only [SExpParser.toProper, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq] at h
            obtain ⟨a', ha, d', hd, rfl⟩ := h
            rw [toSExp2_ofList]
            simp only [List.map_cons, SExp2.ofList]
            rw [ih.1 a a' ha, ih.2 d d' hd]
      · cases e with
        | nil => simp only [SExpParser.toProperList, Option.some.injEq] at h; subst h; rfl
        | atom => simp [SExpParser.toProperList] at h
        | cons a d =>
            simp only [SExpParser.toProperList, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq] at h
            obtain ⟨a', ha, d', hd, rfl⟩ := h
            simp only [List.map_cons, SExp2.ofList]
            rw [ih.1 a a' ha, ih.2 d d' hd]

theorem toPose?_sound {e : Pose2} {p : Pose} (h : e.toPose? = some p) : Pose2.ofPose p = e :=
  (toProper_sound _).1 e p h

end Silmaril.Proofs.Formats.SExp.Pose2
