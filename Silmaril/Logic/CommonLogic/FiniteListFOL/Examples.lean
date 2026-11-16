module

import Lean

public import Silmaril.Logic.CommonLogic.FiniteListFOL.Translation.Thms

/-! Substantive full-Core examples. These are private WIP source examples;
compilation and observed axiom output are pending. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.FiniteListFOL.Examples
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder

/-- Every name class has two symbols. -/
def sig : Core.Signature := ⟨Bool, Bool, Bool⟩

def baseRelation : Sum Bool Bool → List Bool → Prop
  | .inl b, xs => b ∈ xs
  | .inr b, xs => b = true ∧ xs = []

/-- Two discourse values, four references, two marker values, a total
head-sensitive application, and independently extensible predicates. -/
def demo (wide : Bool) : Core.Model sig where
  Reference := Sum Bool Bool
  Discourse := Bool
  nonempty := ⟨false⟩
  embed := Sum.inl
  injective := by intro x y h; exact Sum.inl.inj h
  discourse := id
  nondiscourse := Sum.inr
  outside := by intro n x h; cases h
  sequence b := match (b : Bool) with
    | true => [true, false]
    | false => []
  function r xs := match r with
    | .inl b => b
    | .inr b => xs.headD b
  relation r xs := wide = true ∨ baseRelation r xs

theorem populated_marker : (demo false).sequence true = [true, false] := rfl

theorem extra_reference_outside : ∀ x : Bool,
    (demo false).embed x ≠ (demo false).nondiscourse true :=
  (demo false).outside true

/-- The outer application and predicate heads are computed by an inner
application of the named nondiscourse reference to a nonempty argument list. -/
def computed : Core.Sentence sig :=
  .conj
    (.equal
      (.app (.lift (.app (.nonname true) (.cons (.name false) .nil))) (.marker true))
      (.name false))
    (.pred (.lift (.app (.nonname true) (.cons (.name false) .nil)))
      (.cons (.name false) (.marker true)))

theorem computed_true : (Core.room sig).Sat (demo false) computed := by
  change false = false ∧ (false = true ∨ false ∈ [false, true, false])
  exact ⟨rfl, Or.inr (by simp)⟩

/-- Individual and sequence binders coexist; the arbitrary sequence is
concatenated with a named marker before application and predicate evaluation. -/
def mixed : Core.Sentence sig :=
  .all (.allSeq (.conj
    (.equal (.app (.lift (.var 0)) (.append (.seqvar 0) (.marker true))) (.var 0))
    (.pred (.lift (.var 0)) (.cons (.var 0) (.append (.seqvar 0) (.marker true))))))

theorem mixed_true : (Core.room sig).Sat (demo false) mixed := by
  change ∀ x : Bool, ∀ xs : List Bool,
    x = x ∧ (false = true ∨ x ∈ x :: (xs ++ [true, false]))
  intro x xs
  exact ⟨rfl, Or.inr (by simp)⟩

def someSequence : Core.Sentence sig :=
  .exSeq (.pred (.lift (.name false)) (.append (.seqvar 0) (.marker true)))

theorem someSequence_true : (Core.room sig).Sat (demo false) someSequence := by
  change ∃ xs : List Bool, false = true ∨ false ∈ xs ++ [true, false]
  exact ⟨[], Or.inr (by simp)⟩

/-- This universal fails at the actual empty list. The target cannot omit it. -/
def everySequence : Core.Sentence sig :=
  .allSeq (.pred (.lift (.name false)) (.seqvar 0))

theorem everySequence_false : ¬ (Core.room sig).Sat (demo false) everySequence := by
  change ¬ (∀ xs : List Bool, false = true ∨ false ∈ xs)
  intro h
  simpa using h []

/-- Forward truth transport for the mixed universal sentence. -/
theorem mixed_target_true : (room sig).Sat (expand (demo false)) (sentence mixed) := by
  apply (sentence_holds (expand (demo false)) mixed).mpr
  change (Core.room sig).Sat (decode (expand (demo false))) mixed
  rw [decode_expand]
  exact mixed_true

/-- Reverse truth transport for the same actual-list universal sentence. -/
theorem mixed_target_reflects
    (h : (room sig).Sat (expand (demo false)) (sentence mixed)) :
    (Core.room sig).Sat (demo false) mixed := by
  have hs := (sentence_holds (expand (demo false)) mixed).mp h
  change (Core.room sig).Sat (decode (expand (demo false))) mixed at hs
  rw [decode_expand] at hs
  exact hs

theorem computed_target_true :
    (room sig).Sat (expand (demo false)) (sentence computed) := by
  apply (sentence_holds (expand (demo false)) computed).mpr
  change (Core.room sig).Sat (decode (expand (demo false))) computed
  rw [decode_expand]
  exact computed_true

theorem someSequence_target_true :
    (room sig).Sat (expand (demo false)) (sentence someSequence) := by
  apply (sentence_holds (expand (demo false)) someSequence).mpr
  change (Core.room sig).Sat (decode (expand (demo false))) someSequence
  rw [decode_expand]
  exact someSequence_true

theorem everySequence_target_false :
    ¬ (room sig).Sat (expand (demo false)) (sentence everySequence) := by
  intro h
  have hs := (sentence_holds (expand (demo false)) everySequence).mp h
  apply everySequence_false
  change (Core.room sig).Sat (decode (expand (demo false))) everySequence at hs
  rw [decode_expand] at hs
  exact hs

/-- Rename every symbol class by Boolean negation. -/
def swap : sig ⟶ sig := ⟨Bool.not, Bool.not, Bool.not⟩

theorem swap_nonidentity : swap ≠ 𝟙 sig := by
  intro h
  have bad := congrArg (fun f : sig ⟶ sig => f.discourse false) h
  cases bad

theorem computed_naturality :
    FOL.Sentence.map (FiniteLists.publicMap (signatureMap swap)) (sentence computed) =
      sentence (computed.map swap) := sentence_map swap computed

theorem mixed_naturality :
    FOL.Sentence.map (FiniteLists.publicMap (signatureMap swap)) (sentence mixed) =
      sentence (mixed.map swap) := sentence_map swap mixed

theorem swapped_decode : decode ((reduct swap).obj (expand (demo false))) =
    (Core.Model.reduct swap).obj (demo false) := by
  rw [decode_reduct, decode_expand]

/-- An actual public FOL arrow. Every operation is identical; only the
predicate extension grows. Relation preservation is deliberately one-way. -/
def underlyingArrow : (expand (demo false)).obj.obj ⟶ (expand (demo true)).obj.obj where
  map _ x := x
  map_op := by
    intro n w s o args
    cases o with
    | nil => rfl
    | cons => rfl
    | extra o => cases o <;> rfl
  map_rel := by
    intro n w r args _hr
    cases r
    exact Or.inl rfl

def targetArrow : expand (demo false) ⟶ expand (demo true) :=
  ObjectProperty.homMk (ObjectProperty.homMk underlyingArrow)

noncomputable def decodedArrow :
    decode (expand (demo false)) ⟶ decode (expand (demo true)) := decodeHom targetArrow

theorem decodedArrow_preserves (r : Sum Bool Bool) (xs : List Bool)
    (h : (decode (expand (demo false))).relation r xs) :
    (decode (expand (demo true))).relation r xs := by
  have hn := decodedArrow.relation r xs h
  change (decode (expand (demo true))).relation r (xs.map id) at hn
  have hid : ∀ ys : List Bool, ys.map (id : Bool → Bool) = ys := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => exact congrArg (List.cons y) ih
  exact (congrArg ((decode (expand (demo true))).relation r) (hid xs)).mp hn

/-- Truth at the target of the actual arrow need not hold at its source. -/
theorem decodedArrow_does_not_reflect :
    (decode (expand (demo true))).relation (.inl false) [] ∧
      ¬ (decode (expand (demo false))).relation (.inl false) [] := by
  constructor
  · change true = true ∨ baseRelation (.inl false)
      (FiniteLists.evaluationEquiv (native (demo true)).toModel [])
    exact Or.inl rfl
  · change ¬ (demo false).relation (.inl false)
      (FiniteLists.evaluationEquiv (native (demo false)).toModel [])
    intro h
    have hr := (congrArg ((demo false).relation (.inl false))
      ((native (demo false)).evaluation ([] : List Bool))).mp h
    change false = true ∨ false ∈ ([] : List Bool) at hr
    simp at hr

theorem arrow_model_naturality :
    reduct swap ⋙ models sig = models sig ⋙ Core.Model.reduct swap := models_natural swap

theorem exact_demo_expansion : decode (expand (demo false)) = demo false :=
  decode_expand (demo false)

theorem mixed_theory_sat : Core.Sat ({mixed} : Set (Core.Sentence sig)) := by
  refine ⟨demo false, ?_⟩
  intro p hp
  have heq : p = mixed := Set.mem_singleton_iff.mp hp
  subst p
  exact mixed_true

theorem mixed_target_theory_sat :
    TargetSat (sentence '' ({mixed} : Set (Core.Sentence sig))) :=
  (sat_transport _).mp mixed_theory_sat

theorem false_theory_unsat : Core.Unsat ({.ff} : Set (Core.Sentence sig)) := by
  rintro ⟨M, hM⟩
  exact hM .ff (by simp)

theorem false_target_theory_unsat :
    ¬ TargetSat (sentence '' ({.ff} : Set (Core.Sentence sig))) :=
  (unsat_transport _).mp false_theory_unsat

/-- A genuine quantified contradiction: the same predicate of a concatenated
sequence holds universally and fails at an existential sequence witness. No
literal false constructor occurs in this formula. -/
def quantifiedContradiction : Core.Sentence sig :=
  .conj
    (.allSeq (.pred (.nonname true) (.append (.seqvar 0) (.marker true))))
    (.exSeq (.neg (.pred (.nonname true) (.append (.seqvar 0) (.marker true)))))

theorem quantified_contradiction_false (M : Core.Model sig) :
    ¬ (Core.room sig).Sat M quantifiedContradiction := by
  rintro ⟨hall, xs, hnot⟩
  exact hnot (hall xs)

theorem quantified_theory_unsat :
    Core.Unsat ({quantifiedContradiction} : Set (Core.Sentence sig)) := by
  rintro ⟨M, hM⟩
  exact quantified_contradiction_false M (hM quantifiedContradiction (by simp))

theorem quantified_target_theory_unsat :
    TargetUnsat (sentence '' ({quantifiedContradiction} : Set (Core.Sentence sig))) :=
  (unsat_transport _).mp quantified_theory_unsat

/-- All three name classes may be empty; the semantic discourse remains inhabited. -/
def emptyNames : Core.Signature := ⟨Empty, Empty, Empty⟩

def emptyNamesModel : Core.Model emptyNames where
  Reference := Bool
  Discourse := Unit
  nonempty := ⟨()⟩
  embed := fun _ => false
  injective := fun _ _ _ => Subsingleton.elim _ _
  discourse := Empty.elim
  nondiscourse := Empty.elim
  outside := fun n => n.elim
  sequence := Empty.elim
  function := fun _ _ => ()
  relation := fun _ xs => xs = []

/-- All four binder kinds and individual equality, with the universally bound
sequence deliberately unused. Empty name classes do not remove full contexts. -/
def emptyNamesSentence : Core.Sentence emptyNames :=
  .all (.ex (.allSeq (.exSeq (.conj
    (.equal (.var 0) (.var 1))
    (.pred (.lift (.var 0)) (.seqvar 0))))))

theorem emptyNames_true : (Core.room emptyNames).Sat emptyNamesModel emptyNamesSentence := by
  change ∀ x : Unit, ∃ y : Unit, ∀ _xs : List Unit, ∃ ys : List Unit,
    y = x ∧ ys = []
  intro x
  refine ⟨x, ?_⟩
  intro _xs
  exact ⟨[], rfl, rfl⟩

theorem emptyNames_target_true :
    (room emptyNames).Sat (expand emptyNamesModel) (sentence emptyNamesSentence) := by
  apply (sentence_holds (expand emptyNamesModel) emptyNamesSentence).mpr
  change (Core.room emptyNames).Sat (decode (expand emptyNamesModel)) emptyNamesSentence
  rw [decode_expand]
  exact emptyNames_true

/-- A genuine many-to-one map in every symbol class. -/
def collapsedSig : Core.Signature := ⟨Unit, Unit, Unit⟩

def collapse : sig ⟶ collapsedSig := ⟨fun _ => (), fun _ => (), fun _ => ()⟩

theorem collapse_noninjective : ¬ Function.Injective collapse.discourse := by
  intro h
  have bad : false = true := h rfl
  cases bad

def collapsedSource : Core.Model collapsedSig where
  Reference := Bool
  Discourse := Unit
  nonempty := ⟨()⟩
  embed := fun _ => false
  injective := fun _ _ _ => Subsingleton.elim _ _
  discourse := fun _ => ()
  nondiscourse := fun _ => true
  outside := by intro _ _ h; cases h
  sequence := fun _ => []
  function := fun _ _ => ()
  relation := fun _ xs => xs = []

theorem collapse_computed_naturality :
    FOL.Sentence.map (FiniteLists.publicMap (signatureMap collapse)) (sentence computed) =
      sentence (computed.map collapse) := sentence_map collapse computed

theorem collapse_mixed_naturality :
    FOL.Sentence.map (FiniteLists.publicMap (signatureMap collapse)) (sentence mixed) =
      sentence (mixed.map collapse) := sentence_map collapse mixed

theorem collapse_decode_expansion :
    decode ((reduct collapse).obj (expand collapsedSource)) =
      (Core.Model.reduct collapse).obj collapsedSource := by
  rw [decode_reduct, decode_expand]

/-- This is equality of functors, including every original FOL model arrow. -/
theorem collapse_arrow_naturality :
    reduct collapse ⋙ models sig = models collapsedSig ⋙ Core.Model.reduct collapse :=
  models_natural collapse

-- Observations only: exact output must be inspected after an actual Lean run.
#print axioms append_evaluation
#print axioms decode_expand
#print axioms formula_holds
#print axioms sentence_map
#print axioms models_natural
#print axioms comorphism_modelExpansive
#print axioms decodedArrow_does_not_reflect
#print axioms sat_transport
#print axioms unsat_transport
#print axioms entails_transport
#print axioms quantified_target_theory_unsat

/- Exact dependency sets observed in normal CI run 43285542643. -/
run_elab do
  let selected : Array (Lean.Name × Array Lean.Name) := #[
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.append_evaluation, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.decode_expand, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.formula_holds, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.sentence_map, #[``propext, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.models_natural, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.comorphism_modelExpansive, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.Examples.decodedArrow_does_not_reflect, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.sat_transport, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.unsat_transport, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.entails_transport, #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Silmaril.Logic.CommonLogic.FiniteListFOL.Examples.quantified_target_theory_unsat, #[``propext, ``Classical.choice, ``Quot.sound])]
  for (declaration, expected) in selected do
    let actual ← Lean.collectAxioms declaration
    unless actual.size == expected.size && actual.all (fun ax => expected.contains ax) do
      throwError "Axiom set changed for {declaration}: {actual}; expected {expected}"

end Silmaril.Logic.CommonLogic.FiniteListFOL.Examples
