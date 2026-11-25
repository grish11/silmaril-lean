module

import Silmaril.Courses.Cambridge.L3.DenotationalInstitution
import Silmaril.Courses.Cambridge.L3.Examples
import Mathlib.Data.Fin.VecNotation

/-! # Checked L3 denotational observations -/

namespace Silmaril.Courses.Cambridge.L3.Denotation.Examples

open L3.Examples (recordLabels)

private def sumType : Ty := .sum .int .bool

private def members (i : recordLabels.Index) : Expr :=
  if i = 0 then .pair (.inl (.int 7) sumType) (.int 9) else .bool true

private def memberTypes (i : recordLabels.Index) : Ty :=
  if i = 0 then .prod sumType .int else .bool

private def dataProgram : Expr :=
  .snd (.project (.record recordLabels members) (recordLabels.label 0))

private theorem members_values (i : recordLabels.Index) : IsValue (members i) := by
  by_cases first : i = 0 <;> simp only [members, first, ite_true, ite_false]
  · exact .pair (.inl (.int 7)) (.int 9)
  · exact .bool true

example : HasType ∅ .empty dataProgram .int := by
  apply HasType.snd (A := sumType)
  have recordTyping : HasType ∅ .empty (.record recordLabels members)
      (.record recordLabels memberTypes) := by
    refine .record ?_
    intro i
    by_cases first : i = 0 <;> simp only [memberTypes, members, first, ite_true, ite_false]
    · exact .pair (.inl (.int 7)) (.int 9)
    · exact .bool true
  exact HasType.project (labels := recordLabels) 0 recordTyping

example : DataType.int.Observes dataProgram ∅ 9 ∅ := by
  apply (adequate_data (.snd (.project (.value (.record members_values))))).mpr
  refine .head (.sndStep (.projectValue (labels := recordLabels) 0 members_values)) ?_
  exact .single (.sndValue (.inl (.int 7)) (.int 9))

private def payloadLabel : RecordLabels := ⟨["payload"], by decide⟩

private def payloadType : DataType (.record payloadLabel (fun _ => .prod sumType .int)) :=
  .record (fun _ => .prod (.sum .int .bool) .int)

example : payloadType.Observes
    (.record payloadLabel (fun _ => .pair (.inl (.int 7) sumType) (.int 9)))
    ∅ (fun _ => (.inl 7, 9)) ∅ := by
  apply (adequate_data (.value (.record (fun _ => .pair (.inl (.int 7)) (.int 9))))).mpr
  exact .refl

-- Every fresh allocation branch produces the same ground answer and its own store.
private theorem read_new_cell (s : Store) (a : Loc) (fresh : a ∉ s) :
    DataType.int.Observes (.deref (.ref (.int 42))) s 42 (s.insert a (integer 42)) := by
  change Returns (denote (.ref (.int 42)) >>= read) s (integer 42) (s.insert a (integer 42))
  apply (returns_bind _ _ _ _ _).mpr
  refine ⟨address a, s.insert a (integer 42), ?_, ?_⟩
  · simp only [denote, denoteWith, pure_bind]
    exact ⟨a, fresh, rfl⟩
  · change (s.insert a (integer 42)).lookup a = some (integer 42) ∧ _
    exact ⟨by simp, rfl⟩

example :
    DataType.int.Observes (.deref (.ref (.int 42))) ∅ 42 ((∅ : Store).insert 0 (integer 42)) ∧
    DataType.int.Observes (.deref (.ref (.int 42))) ∅ 42 ((∅ : Store).insert 1 (integer 42)) ∧
    (∅ : Store).insert 0 (integer 42) ≠ (∅ : Store).insert 1 (integer 42) := by
  refine ⟨read_new_cell ∅ 0 Finmap.notMem_empty, read_new_cell ∅ 1 Finmap.notMem_empty, ?_⟩
  intro same
  have lookup := congrArg (fun s : Store => s.lookup 0) same
  simp [Finmap.lookup_insert_of_ne] at lookup

-- Allocation cannot return an address that was already in the input store.
example (s t : Store) (a : Loc) (present : a ∈ s) :
    ¬ Returns (denote (.ref (.int 42))) s (address a) t := by
  simp only [denote, denoteWith, pure_bind]
  intro returned
  change ∃ b, b ∉ s ∧ (address a, t) = (address b, s.insert b (integer 42)) at returned
  obtain ⟨b, fresh, equal⟩ := returned
  have same : a = b := Expr.loc.inj (congrArg Subtype.val (congrArg Prod.fst equal))
  exact fresh (same ▸ present)

-- Projection evaluates both record writes, retaining the second write's store.
example :
    DataType.unit.Observes L3.Examples.recordProgram ((∅ : Store).insert 0 L3.Examples.zero) ()
      ((∅ : Store).insert 0 L3.Examples.two) := by
  apply (adequate_data ?_).mpr L3.Examples.recordProgram_trace
  refine .project (.record ?_)
  intro i
  by_cases first : i = 0 <;> simp only [L3.Examples.writes, first, ite_true, ite_false]
  · exact .assign (.value (.loc 0)) (.value (.int 1))
  · exact .assign (.value (.loc 0)) (.value (.int 2))

private def flagStore : Store := (∅ : Store).insert 0 (boolean true)

private def flagTest : Expr := .deref (.loc 0)

private def allocateAndStop : Expr :=
  .seq (.assign (.ref (.int 11)) (.int 42)) (.assign (.loc 0) (.bool false))

private def allocateOnce : Expr := .loop flagTest allocateAndStop

private theorem allocateOnce_fragment : Fragment allocateOnce :=
  .loop (.deref (.value (.loc 0)))
    (.seq (.assign (.ref (.value (.int 11))) (.value (.int 42)))
      (.assign (.value (.loc 0)) (.value (.bool false))))

example : HasType ((∅ : LocTypes).insert 0 .bool) .empty allocateOnce .unit :=
  .loop (.deref (.loc (by simp))) (.seq (.assign (.ref (.int 11)) (.int 42))
    (.assign (.loc (by simp)) (.bool false)))

-- One iteration allocates, initializes the new cell, and clears the guard.
-- The final store depends on the fresh address selected during that iteration.
example (a : Loc) (fresh : a ∉ flagStore) :
    DataType.unit.Observes allocateOnce flagStore ()
      ((flagStore.insert a (integer 42)).insert 0 (boolean false)) := by
  apply (adequate_data allocateOnce_fragment).mpr
  let allocated := flagStore.insert a (integer 11)
  let written := flagStore.insert a (integer 42)
  let final := written.insert 0 (boolean false)
  have flagOn : flagStore.lookup 0 = some (boolean true) := by simp [flagStore]
  have allocatedStep : Step ⟨.ref (.int 11), flagStore⟩ ⟨.loc a, allocated⟩ :=
    .refValue (integer 11) fresh
  have writeStep : Step ⟨.assign (.loc a) (.int 42), allocated⟩ ⟨.skip, written⟩ := by
    change Step ⟨.assign (.loc a) (integer 42).val, allocated⟩ ⟨.skip, written⟩
    simpa only [allocated, written, Finmap.insert_insert] using
      (Step.assignValue (integer 42) (s := allocated) (loc := a) (by simp [allocated]))
  have clearStep : Step ⟨.assign (.loc 0) (.bool false), written⟩ ⟨.skip, final⟩ :=
    .assignValue (boolean false) (by simp [written, flagStore])
  have flagOff : final.lookup 0 = some (boolean false) := by simp [final]
  refine .head .while (.head (.ifStep (.derefValue flagOn)) (.head .ifTrue ?_))
  refine .head (.seqStep (.seqStep (.assignLeft allocatedStep))) ?_
  refine .head (.seqStep (.seqStep writeStep)) (.head (.seqStep .seqSkip) ?_)
  refine .head (.seqStep clearStep) (.head .seqSkip ?_)
  exact .head .while (.head (.ifStep (.derefValue flagOff)) (.single .ifFalse))

private theorem rightCaseFragment : Fragment L3.Examples.sumProgram :=
  .matchSum (.value (.inr (.bool true))) (.bvar 0)
    (.cond (.bvar 0) (.fst (.value (.pair (.int 5) (.bool false)))) (.value (.int 0)))

example : DataType.int.Observes L3.Examples.sumProgram ∅ 5 ∅ :=
  (adequate_data rightCaseFragment).mpr L3.Examples.sumProgram_trace

/-- The left branch has the payload at index 0 and the outer cell at index 1.
The right branch would allocate a second cell if selected. -/
private def lexicalWrite : Expr :=
  .letE (.ref .int) (.ref (.int 5))
    (.matchSum (.inl (.int 12) (.sum .int .unit)) .int
      (.seq (.assign (.bvar 1) (.bvar 0)) (.deref (.bvar 1)))
      .unit (.deref (.ref (.int 99))))

private theorem lexicalWrite_fragment : Fragment lexicalWrite :=
  .letE (.ref (.value (.int 5)))
    (.matchSum (.value (.inl (.int 12)))
      (.seq (.assign (.bvar 1) (.bvar 0)) (.deref (.bvar 1)))
      (.deref (.ref (.value (.int 99)))))

example : HasType ∅ .empty lexicalWrite .int :=
  .letE (.ref (.int 5))
    (.matchSum (.inl (.int 12))
      (.seq (.assign (.bvar rfl) (.bvar rfl)) (.deref (.bvar rfl)))
      (.deref (.ref (.int 99))))

private theorem lexicalWrite_returns (s : Store) (a : Loc) (fresh : a ∉ s) :
    DataType.int.Observes lexicalWrite s 12 (s.insert a (integer 12)) := by
  unfold DataType.Observes denote
  rw [lexicalWrite, denoteWith]
  apply (returns_bind _ _ _ _ _).mpr
  refine ⟨address a, s.insert a (integer 5), ?_, ?_⟩
  · simp only [denoteWith, pure_bind]
    exact ⟨a, fresh, rfl⟩
  · simp only [denoteWith, pure_bind, splitSum, injectLeft, Environment.extend,
      Binding.denote, assign, address]
    apply (returns_bind _ _ _ _ _).mpr
    refine ⟨unit, s.insert a (integer 12), ?_, ?_⟩
    · change a ∈ s.insert a (integer 5) ∧
        (unit, s.insert a (integer 12)) = (unit, (s.insert a (integer 5)).insert a (integer 12))
      simp
    · change (s.insert a (integer 12)).lookup a = some (integer 12) ∧ _
      exact ⟨by simp, rfl⟩

private def lexicalSource : Config := ⟨lexicalWrite, ∅⟩

private def lexicalTarget (a : Loc) : Config := ⟨.int 12, (∅ : Store).insert a (integer 12)⟩

private abbrev lexicalContext : StepSpecification.Context := ⟨.l3, 3⟩

private def lexicalCatalogue : StepSpecification.Catalogue lexicalContext :=
  ![lexicalSource, lexicalTarget 0, lexicalTarget 1]

private def lexicalClaims : ReturnSpecification.Sentence lexicalContext :=
  [.mayReturn 0, .mayReturnTo 0 1, .mayReturnTo 0 2]

-- The catalogue institution distinguishes the concrete final stores for the same typed answer.
example : ReturnSpecification.Holds lexicalContext lexicalCatalogue lexicalClaims ∧
    lexicalTarget 0 ≠ lexicalTarget 1 := by
  have observes (a : Loc) : DenotationalInstitution.observesReturn lexicalSource (lexicalTarget a) :=
    ⟨integer 12, rfl, lexicalWrite_returns ∅ a Finmap.notMem_empty⟩
  refine ⟨(DenotationalInstitution.holds_iff lexicalCatalogue lexicalClaims ?_).mpr ?_, ?_⟩
  · intro claim member
    simp only [lexicalClaims, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact lexicalWrite_fragment
  · intro claim member
    simp only [lexicalClaims, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨lexicalTarget 0, observes 0⟩
    · exact observes 0
    · exact observes 1
  · intro equal
    have lookup := congrArg (fun c : Config => c.store.lookup 0) equal
    simp [lexicalTarget, Finmap.lookup_insert_of_ne] at lookup

private def capturesOuter : Expr :=
  .letE .int (.int 7) (.ref (.lam .int (.binary (.bvar 1) .add (.bvar 0))))

private def captured : Value :=
  ⟨.lam .int (.binary (.int 7) .add (.bvar 0)), .lam _ _⟩

-- Quoting an opaque function captures the lexical value and preserves its parameter binder.
example (s : Store) (a : Loc) (fresh : a ∉ s) :
    Returns (denote capturesOuter) s (address a) (s.insert a captured) := by
  simp only [denote, capturesOuter, denoteWith, pure_bind]
  exact ⟨a, fresh, rfl⟩

end Silmaril.Courses.Cambridge.L3.Denotation.Examples
