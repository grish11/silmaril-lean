module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closure.Body

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure.Body

theorem childPaths {tree : Source.ScopeTree} {start : Nat} {source : List Source.Stmt}
    {code : Code (Compile.Closure.frameLayout tree.scope)} (translated : Translation tree start source code) :
    code.childPaths.Nodup ∧ ∀ path ∈ code.childPaths,
      ∃ index suffix, start ≤ index ∧ path = tree.scope.context.path ++ index :: suffix := by
  induction translated with
  | ret => simp [Code.childPaths]
  | assign _ _ _ _ tail => exact tail
  | nonlocal _ tail => exact tail
  | @closure tree start name declaration body rest slot child params code next _ path _ _ _ _ _ _ _ inner tail =>
    let parent := tree.scope.context.path
    have nestedPath {nested : Source.BlockPath} (member : nested ∈ code.childPaths) :
        ∃ suffix : Source.BlockPath, nested = parent ++ start :: suffix ∧ suffix ≠ [] := by
      obtain ⟨index, suffix, _, located⟩ := inner.2 nested member
      refine ⟨index :: suffix, ?_, by simp⟩
      simpa only [path, List.append_assoc, List.singleton_append] using located
    have laterPath {later : Source.BlockPath} (member : later ∈ next.childPaths) :
        ∃ index suffix, start < index ∧ later = parent ++ index :: suffix :=
      tail.2 later member
    have separate : List.Disjoint code.childPaths next.childPaths := by
      intro candidate inside after
      obtain ⟨suffix, found, _⟩ := nestedPath inside
      obtain ⟨index, rest, later, elsewhere⟩ := laterPath after
      have clash := List.append_cancel_left (found.symm.trans elsewhere)
      exact (Nat.ne_of_lt later) (List.cons.inj clash).1
    have distinct : parent ++ [start] ∉ code.childPaths ++ next.childPaths := by
      intro member
      rcases List.mem_append.mp member with innerMember | tailMember
      · obtain ⟨suffix, found, nonempty⟩ := nestedPath innerMember
        exact nonempty (List.cons.inj (List.append_cancel_left found)).2.symm
      · obtain ⟨index, rest, later, elsewhere⟩ := laterPath tailMember
        exact (Nat.ne_of_lt later) (List.cons.inj (List.append_cancel_left elsewhere)).1
    refine ⟨List.nodup_cons.mpr ⟨distinct, inner.1.append tail.1 separate⟩, ?_⟩
    intro candidate member
    rcases List.mem_cons.mp member with own | others
    · exact ⟨start, [], Nat.le_refl _, own⟩
    rcases List.mem_append.mp others with innerMember | tailMember
    · obtain ⟨suffix, located, _⟩ := nestedPath innerMember
      exact ⟨start, suffix, Nat.le_refl _, located⟩
    · obtain ⟨index, suffix, later, located⟩ := laterPath tailMember
      exact ⟨index, suffix, Nat.le_of_lt later, located⟩

theorem paths_distinct {source : Source.Module} (compiled : Compiled source) : compiled.paths.Nodup := by
  have paths := childPaths compiled.translated
  refine List.nodup_cons.mpr ⟨?_, paths.1⟩
  intro member
  obtain ⟨index, suffix, _, located⟩ := paths.2 _ member
  have impossible := congrArg List.length located
  simp at impossible

end Silmaril.Proofs.Languages.Python.Compile.Closure.Body
