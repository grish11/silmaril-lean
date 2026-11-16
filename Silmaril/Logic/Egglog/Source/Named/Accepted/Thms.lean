module

public import Silmaril.Logic.Egglog.Source.Named.Accepted.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named

theorem AcceptedSentence.resolved_holds {D : Declarations} (sentence : AcceptedSentence D)
    (M : Core.Model D.signature) : sentence.resolved.Holds M ↔ sentence.Holds M :=
  (resolveSentence_holds_iff D sentence.raw sentence.resolved sentence.resolve_eq M).symm

/-- Whole-program compilation compares every original rule and existential query
in the same actual model. No distinguished entry stands for the program. -/
theorem AcceptedProgram.resolved_holds (program : AcceptedProgram)
    (M : Core.Model program.declarations.signature) :
    program.Holds M ↔ ∀ sentence ∈ program.resolved, sentence.Holds M :=
  mapM_forall_iff _ program.raw.sentences program.resolved program.resolve_eq _ _
    (fun raw resolved success =>
      resolveSentence_holds_iff program.declarations raw resolved success M)

/-- Successful compilation preserves the complete ordered list length. -/
theorem mapM_length {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (success : xs.mapM f = some ys) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => simp at success; subst ys; rfl
  | cons first rest ih =>
      cases hf : f first with
      | none => simp [hf] at success
      | some value =>
          cases hr : rest.mapM f with
          | none => simp [hf, hr] at success
          | some tail =>
              simp [hf, hr] at success
              subst ys
              exact congrArg Nat.succ (ih tail hr)

/-- The compiler result at each original position is the corresponding sentence,
not merely a member of an unordered image. -/
theorem mapM_get {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (success : xs.mapM f = some ys) (index : Fin xs.length) :
    f (xs.get index) = some (ys.get (Fin.cast (mapM_length f xs ys success) index)) := by
  induction xs generalizing ys with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      cases hf : f first with
      | none => simp [hf] at success
      | some value =>
          cases hr : rest.mapM f with
          | none => simp [hf, hr] at success
          | some tail =>
              simp [hf, hr] at success
              subst ys
              rcases index with ⟨index, bound⟩
              cases index with
              | zero => exact hf
              | succ index =>
                  exact ih tail hr ⟨index, Nat.lt_of_succ_lt_succ bound⟩

def ProgramEntry.compiledIndex (entry : ProgramEntry) : Fin entry.program.resolved.length :=
  Fin.cast (mapM_length _ _ _ entry.program.resolve_eq) entry.index

def ProgramEntry.resolved (entry : ProgramEntry) :
    Core.Sentence entry.program.declarations.signature :=
  entry.program.resolved.get entry.compiledIndex

theorem ProgramEntry.resolve_eq (entry : ProgramEntry) :
    resolveSentence? entry.program.declarations entry.raw = some entry.resolved :=
  mapM_get _ _ _ entry.program.resolve_eq entry.index

theorem ProgramEntry.resolved_holds (entry : ProgramEntry)
    (M : Core.Model entry.program.declarations.signature) :
    entry.resolved.Holds M ↔ entry.raw.Holds M :=
  (resolveSentence_holds_iff _ _ _ entry.resolve_eq M).symm

end Silmaril.Logic.Egglog.Source.Named
