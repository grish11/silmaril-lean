module

import Silmaril.Courses.Cambridge.ReturnSpecification.Format
import Mathlib.Data.Fin.VecNotation
meta import Silmaril.Courses.Cambridge.ReturnSpecification.Format

/-! Full-store returns, multiple L3 witnesses, and checked format translations. -/

namespace Silmaril.Courses.Cambridge.ReturnSpecification.Examples

open Silmaril.Courses.Cambridge.StepSpecification (Context Catalogue)
open Silmaril.Courses.Cambridge.AstCodec (Tree node)

private abbrev l1Context : Context := ⟨.l1, 2⟩
private def beforeStore : L1.Store := L1.Store.empty.insert "x" 7
private def afterStore : L1.Store := beforeStore.insert "x" 42

private def l1Catalogue : Catalogue l1Context :=
  ![⟨.assign "x" (.int 42), beforeStore⟩, ⟨.skip, afterStore⟩]

private def l1Good : Sentence l1Context := [.mayReturnTo 0 1, .mayReturnTo 1 1]
private def l1Bad : Sentence l1Context := [.mayReturnTo 0 0]

example : Holds l1Context l1Catalogue l1Good := by
  apply (holds_iff _ _ _).2
  intro claim member
  have either : claim = .mayReturnTo 0 1 ∨ claim = .mayReturnTo 1 1 := by
    simpa [l1Good] using member
  rcases either with equal | equal <;> subst claim
  · exact ⟨.single (.assignValue (by simp [beforeStore])), .skip⟩
  · exact ⟨.refl, .skip⟩

private theorem l1False : ¬ Holds l1Context l1Catalogue l1Bad := by
  intro holds
  have returned := (holds_iff _ _ _).1 holds (.mayReturnTo 0 0) (by simp [l1Bad])
  change Returns .l1 (l1Catalogue 0) (l1Catalogue 0) at returned
  have value := returned.2
  change L1.IsValue (.assign "x" (.int 42)) at value
  cases value

-- A well-formed false claim stays false through format translation.
example : ∃ proposition,
    (jsonToSExp l1Context ((json l1Context).encode l1Bad)).bind
      (meaningSExp l1Context l1Catalogue) = some proposition ∧ ¬ proposition := by
  refine ⟨Holds l1Context l1Catalogue l1Bad, ?_, l1False⟩
  rw [jsonToSExp_meaning]
  unfold meaningJson
  rw [(json l1Context).recovers]
  rfl

private abbrev l2Context : Context := ⟨.l2, 3⟩

private def l2Catalogue : Catalogue l2Context :=
  ![⟨.app (.lam .int (.bvar 0)) (.deref "x"), afterStore⟩,
    ⟨.app (.lam .int (.bvar 0)) (.int 42), afterStore⟩,
    ⟨.int 42, afterStore⟩]

private theorem l2Argument : L2.Step (l2Catalogue 0) (l2Catalogue 1) :=
  .appRight (.lam _ _) (.deref (by simp [afterStore]))

private theorem l2Beta : L2.Step (l2Catalogue 1) (l2Catalogue 2) := .appFun (.int 42)

example : Holds l2Context l2Catalogue [.mayReturnTo 0 2] := by
  apply (holds_iff _ _ _).2
  intro claim member
  have equal : claim = .mayReturnTo 0 2 := List.mem_singleton.mp member
  subst claim
  exact ⟨.tail (.single l2Argument) l2Beta, .int 42⟩

private def initialHeap : L3.Store := (∅ : L3.Store).insert 0 ⟨.int 7, .int 7⟩
private def cellValue : L3.Value := ⟨.int 42, .int 42⟩
private def l3Start : L3.Config := ⟨.deref (.ref (.int 42)), initialHeap⟩
private def l3Result (address : L3.Loc) : L3.Config :=
  ⟨.int 42, initialHeap.insert address cellValue⟩

private theorem l3Return (address : L3.Loc) (fresh : address ∉ initialHeap) :
    Returns .l3 l3Start (l3Result address) := by
  refine ⟨.tail (.single (.derefStep (.refValue cellValue fresh))) ?_, .int 42⟩
  exact .derefValue (value := cellValue) (by simp)

private theorem firstReturn : Returns .l3 l3Start (l3Result 1) :=
  l3Return 1 (by simp [initialHeap, Finmap.notMem_empty])

private theorem secondReturn : Returns .l3 l3Start (l3Result 2) :=
  l3Return 2 (by simp [initialHeap, Finmap.notMem_empty])

private abbrev sourceContext : Context := ⟨.l3, 1⟩
private def sourceCatalogue : Catalogue sourceContext := fun _ => l3Start

-- Both witnesses belong to the same existential claim, whose catalogue
-- names only the source.
example : Holds sourceContext sourceCatalogue [.mayReturn 0] ∧
    ∃ first second : L3.Config, first.expr = second.expr ∧ first.store ≠ second.store ∧
      (semantics .l3).May (sourceCatalogue 0) (.returned first) ∧
      (semantics .l3).May (sourceCatalogue 0) (.returned second) := by
  refine ⟨(holds_iff _ _ _).2 ?_, l3Result 1, l3Result 2, rfl, ?_, ?_, ?_⟩
  · intro claim member
    have equal : claim = .mayReturn 0 := List.mem_singleton.mp member
    subst claim
    exact ⟨l3Result 1, firstReturn⟩
  · intro equal
    have lookup := congrArg (fun heap : L3.Store => heap.lookup 1) equal
    simp [l3Result, initialHeap, Finmap.lookup_insert_of_ne] at lookup
  · exact (may_return_iff _ _ _).2 firstReturn
  · exact (may_return_iff _ _ _).2 secondReturn

private abbrev l3Context : Context := ⟨.l3, 3⟩
private def l3Catalogue : Catalogue l3Context := ![l3Start, l3Result 1, l3Result 2]
private def l3Both : Sentence l3Context := [.mayReturnTo 0 1, .mayReturnTo 0 2]

example :
    (observationLogic.obj (signature l3Context.language.Config)).Sat
      (observationModel l3Context.language) ((translation l3Context l3Catalogue).sen l3Both) := by
  apply (satisfaction l3Context l3Catalogue l3Both).2
  apply (holds_iff _ _ _).2
  intro claim member
  have either : claim = .mayReturnTo 0 1 ∨ claim = .mayReturnTo 0 2 := by
    simpa [l3Both] using member
  rcases either with equal | equal <;> subst claim
  · exact firstReturn
  · exact secondReturn

private def returnDoc : Lean.Json :=
  .arr #[.str "cambridge-may-return-spec-v1", .str "L3", .str "3",
    .arr #[.str "all", .arr #[.str "may-return-to", .str "0", .str "1"],
      .arr #[.str "may-return-to", .str "0", .str "2"]]]

private def returnSExp : Tree :=
  node "cambridge-may-return-spec-v1" [.atom "L3", .atom "3", node "all"
    [node "may-return-to" [.atom "0", .atom "1"], node "may-return-to" [.atom "0", .atom "2"]]]

#guard (json l3Context).encode l3Both == returnDoc
#guard (sexp l3Context).decode? returnSExp = some l3Both
#guard (jsonToSExp l3Context returnDoc).bind (sexp l3Context).decode? = some l3Both
#guard sexpToJson l3Context returnSExp == some returnDoc
#guard (jsonBytes l3Context).decode? ((jsonBytes l3Context).encode l3Both) = some l3Both

private def invalidSExp : Tree :=
  node "cambridge-may-return-spec-v1" [.atom "L3", .atom "1",
    node "all" [node "may-return-to" [.atom "0", .atom "1"]]]

#guard (sexpToJson sourceContext invalidSExp).isNone
#guard (meaningSExp sourceContext sourceCatalogue invalidSExp).isNone
private def anyReturnDoc : Lean.Json :=
  .arr #[.str "cambridge-may-return-spec-v1", .str "L3", .str "1",
    .arr #[.str "all", .arr #[.str "may-return", .str "0"]]]

#guard (jsonToSExp sourceContext anyReturnDoc).bind (sexp sourceContext).decode? =
  some [.mayReturn 0]
#guard (jsonToSExp l2Context returnDoc).isNone

private def existingStepDoc : Lean.Json :=
  .arr #[.str "cambridge-step-spec-v1", .str "L1", .str "2",
    .arr #[.str "all", .arr #[.str "step", .str "0", .str "1"]]]

#guard (StepSpecification.json l1Context).decode? existingStepDoc = some [(0, (), 1)]
#guard (jsonToSExp l1Context existingStepDoc).isNone
#guard ((StepSpecification.json l3Context).decode? returnDoc).isNone

end Silmaril.Courses.Cambridge.ReturnSpecification.Examples
