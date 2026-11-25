module

import Silmaril.Courses.Cambridge.StepSpecification.Format
import Silmaril.Courses.Cambridge.L1.Codec
import Silmaril.Courses.Cambridge.L1.Metatheory.Determinacy
import Mathlib.Data.Fin.VecNotation
meta import Silmaril.Courses.Cambridge.StepSpecification.Format
meta import Silmaril.Courses.Cambridge.L1.Codec

/-! Decoding and truth are checked separately on actual course configurations. -/

namespace Silmaril.Courses.Cambridge.StepSpecification.Examples

open CategoryTheory Silmaril.Logic.Institution

private def step (source target : String) : Lean.Json :=
  .arr #[.str "step", .str source, .str target]

private def document (lang slots : String) (claims : Array Lean.Json) : Lean.Json :=
  .arr #[.str "cambridge-step-spec-v1", .str lang, .str slots, .arr (#[.str "all"] ++ claims)]

private abbrev l1Context : Context := ⟨.l1, 3⟩
private def beforeStore : L1.Store := L1.Store.empty.insert "x" 7
private def afterStore : L1.Store := beforeStore.insert "x" 42

private def l1Catalogue : Catalogue l1Context :=
  ![⟨.assign "x" (.int 42), beforeStore⟩, ⟨.skip, afterStore⟩, ⟨.skip, beforeStore⟩]

private def l1Good : Sentence l1Context := [(0, (), 1)]
private def l1Stale : Sentence l1Context := [(0, (), 2)]

#guard (json l1Context).encode l1Good == document "L1" "3" #[step "0" "1"]
#guard ((json l1Context).decode? (document "L1" "3" #[step "0" "2"])).isSome

private theorem l1Assign : L1.Step (l1Catalogue 0) (l1Catalogue 1) :=
  .assignValue (by simp [beforeStore])

private theorem l1GoodHolds : Holds l1Context l1Catalogue l1Good := by
  apply (holds_iff _ _ _).2
  intro edge member
  have equal : edge = (0, (), 1) := List.mem_singleton.mp member
  subst edge
  exact l1Assign

example :
    (operationalLogic.obj l1Context.language.system.shape).Sat
      (Discrete.mk l1Context.language.system.model) ((translation l1Context l1Catalogue).sen l1Good) :=
  (satisfaction _ _ _).2 l1GoodHolds

private theorem staleFalse : ¬ Holds l1Context l1Catalogue l1Stale := by
  intro sat
  have wrong := (holds_iff _ _ _).1 sat (0, (), 2) (by simp [l1Stale])
  have equal := L1.Step.deterministic l1Assign wrong
  have lookup := congrArg (fun c : L1.Config => c.store.lookup "x") equal
  change afterStore.lookup "x" = beforeStore.lookup "x" at lookup
  simp [afterStore, beforeStore] at lookup

example : ∃ claim, meaning l1Context l1Catalogue ((json l1Context).encode l1Stale) =
    some claim ∧ ¬ claim :=
  ⟨_, meaning_encode _ _ _, staleFalse⟩

#guard (meaning l1Context l1Catalogue (document "L1" "3" #[step "0" "3"])).isNone

private abbrev smaller : Context := ⟨.l1, 2⟩
private def includeNames : smaller ⟶ l1Context :=
  ⟨rfl, fun i => ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩⟩

example : (institution.map includeNames).sen ([(0, (), 1)] : Sentence smaller) =
    ([(1, (), 2)] : Sentence l1Context) := rfl

private abbrev l2Context : Context := ⟨.l2, 3⟩
private def l2Catalogue : Catalogue l2Context :=
  ![⟨.app (.lam .int (.bvar 0)) (.deref "x"), afterStore⟩,
    ⟨.app (.lam .int (.bvar 0)) (.int 42), afterStore⟩, ⟨.int 42, afterStore⟩]

private def l2Good : Sentence l2Context := [(0, (), 1), (1, (), 2)]

#guard (json l2Context).encode l2Good == document "L2" "3" #[step "0" "1", step "1" "2"]

example : Holds l2Context l2Catalogue l2Good := by
  apply (holds_iff _ _ _).2
  intro edge member
  have oneOf : edge = (0, (), 1) ∨ edge = (1, (), 2) := by simpa [l2Good] using member
  rcases oneOf with equal | equal <;> subst edge
  · exact L2.Step.appRight (.lam _ _) (.deref (by simp [afterStore]))
  · exact L2.Step.appFun (.int 42)

example : ¬ Holds l2Context l2Catalogue [(0, (), 2)] := by
  intro sat
  have direct := (holds_iff _ _ _).1 sat (0, (), 2) (by simp)
  change L2.Step ⟨.app (.lam .int (.bvar 0)) (.deref "x"), afterStore⟩
    ⟨.int 42, afterStore⟩ at direct
  cases direct

private abbrev l3Context : Context := ⟨.l3, 4⟩
private def initialHeap : L3.Store := (∅ : L3.Store).insert 0 ⟨.int 7, .int 7⟩
private def cellValue : L3.Value := ⟨.int 42, .int 42⟩

private def l3Catalogue : Catalogue l3Context :=
  ![⟨.ref (.int 42), initialHeap⟩,
    ⟨.loc 1, initialHeap.insert 1 cellValue⟩,
    ⟨.loc 2, initialHeap.insert 2 cellValue⟩,
    ⟨.loc 0, initialHeap.insert 0 cellValue⟩]

private def l3Good : Sentence l3Context := [(0, (), 1), (0, (), 2)]

#guard (json l3Context).encode l3Good == document "L3" "4" #[step "0" "1", step "0" "2"]

example : Holds l3Context l3Catalogue l3Good := by
  apply (holds_iff _ _ _).2
  intro edge member
  have oneOf : edge = (0, (), 1) ∨ edge = (0, (), 2) := by simpa [l3Good] using member
  rcases oneOf with equal | equal <;> subst edge
  · exact L3.Step.refValue cellValue (by simp [initialHeap, Finmap.notMem_empty])
  · exact L3.Step.refValue cellValue (by simp [initialHeap, Finmap.notMem_empty])

private theorem l3Occupied (store : L3.Store) :
    ¬ L3.Step ⟨.ref (.int 42), initialHeap⟩ ⟨.loc 0, store⟩ := by
  intro occupied
  generalize L3.Expr.int 42 = operand at occupied
  cases occupied with
  | refValue _ fresh => exact fresh (by simp [initialHeap])

example : ¬ Holds l3Context l3Catalogue [(0, (), 3)] := by
  intro sat
  exact l3Occupied _ ((holds_iff _ _ _).1 sat (0, (), 3) (by simp))

example : Holds l3Context l3Catalogue [] :=
  (holds_iff _ _ _).2 (by simp)

#guard ((json l1Context).decode? (document "L2" "3" #[step "0" "1"])).isNone
#guard ((json l1Context).decode? (document "L1" "4" #[step "0" "1"])).isNone
#guard ((json l1Context).decode? (document "L1" "3" #[step "-1" "1"])).isNone
#guard ((json l1Context).decode? (document "L1" "3" #[step "0" "01"])).isNone
#guard ((json l1Context).decode? (document "L1" "3" #[.arr #[.str "step", .str "0"]])).isNone
#guard ((json l1Context).decode? (document "L1" "3" #[.arr #[.str "step", .num 0, .str "1"]])).isNone
#guard ((json l1Context).decode? (L1.Codec.termJson.encode (.deref "x"))).isNone

private def staleText : Silmaril.Formats.Bytes :=
  ⟨" [\"cambridge-step-spec-v1\", \"L1\", \"3\", [\"all\", [\"step\", \"0\", \"2\"]]] ".toUTF8⟩

#guard (jsonBytes l1Context).decode? staleText = some l1Stale
#guard (meaningBytes l1Context l1Catalogue staleText).isSome
#guard (meaningBytes l1Context l1Catalogue (staleText.push 0xff)).isNone
#guard (jsonBytes l3Context).decode? ((jsonBytes l3Context).encode l3Good) = some l3Good

example : ∃ claim, meaningBytes l1Context l1Catalogue ((jsonBytes l1Context).encode l1Stale) =
    some claim ∧ ¬ claim :=
  ⟨_, meaningBytes_encode _ _ _, staleFalse⟩

end Silmaril.Courses.Cambridge.StepSpecification.Examples
