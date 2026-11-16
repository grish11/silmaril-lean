module

public import Silmaril.Logic.Egglog.Source.Named.Representation.Support.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.FiniteSupport
open Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem Footprint.subset_refl {S : Core.Signature} (support : Footprint S) :
    support.Subset support := ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Footprint.subset_trans {S : Core.Signature} {left middle right : Footprint S}
    (first : left.Subset middle) (second : middle.Subset right) : left.Subset right :=
  ⟨fun _ h => second.1 _ (first.1 _ h), fun _ h => second.2.1 _ (first.2.1 _ h),
    fun _ h => second.2.2.1 _ (first.2.2.1 _ h),
    fun _ h => second.2.2.2 _ (first.2.2.2 _ h)⟩

theorem Footprint.subset_append_left {S : Core.Signature} (left right : Footprint S) :
    left.Subset (left.append right) :=
  ⟨fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h,
    fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h⟩

theorem Footprint.subset_append_right {S : Core.Signature} (left right : Footprint S) :
    right.Subset (left.append right) :=
  ⟨fun _ h => List.mem_append_right _ h, fun _ h => List.mem_append_right _ h,
    fun _ h => List.mem_append_right _ h, fun _ h => List.mem_append_right _ h⟩

theorem Footprint.merge_contains {S : Core.Signature} {support : Footprint S}
    {entries : List (Footprint S)} (member : support ∈ entries) :
    support.Subset (Footprint.merge entries) := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      change support.Subset (first.append (Footprint.merge rest))
      rcases List.mem_cons.mp member with rfl | tail
      · exact Footprint.subset_append_left _ _
      · exact (Footprint.subset_trans (ih tail) (Footprint.subset_append_right _ _))

/-- Syntactic support is monotone under finite vocabulary extension. -/
theorem SupportsTerm.mono {S : Core.Signature} {left right : Footprint S}
    (subset : left.Subset right) {n : Nat} {Γ : Fin n → S.S} {s : S.S}
    (expression : EQ.Term S.toSignature Γ s) :
    SupportsTerm left expression → SupportsTerm right expression := by
  refine EQ.Term.rec (motive := fun _ expression =>
    SupportsTerm left expression → SupportsTerm right expression) ?_ ?_ expression
  · intro i supported
    exact subset.1 _ supported
  · intro k w output symbol arguments ih supported
    obtain ⟨result, inputs, constructor, children⟩ := supported
    exact ⟨subset.1 _ result, fun i => subset.1 _ (inputs i),
      subset.2.1 _ constructor, fun i => ih i (children i)⟩

/-- Every total term has finite support containing its complete symbol profiles. -/
theorem term_supports {S : Core.Signature} {n : Nat} {Γ : Fin n → S.S} {s : S.S}
    (expression : EQ.Term S.toSignature Γ s) : SupportsTerm (term expression) expression := by
  refine EQ.Term.rec (motive := fun _ expression =>
    SupportsTerm (term expression) expression) ?_ ?_ expression
  · intro i
    exact List.mem_singleton_self _
  · intro k w output symbol arguments ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [term, Footprint.append]
    · intro i
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    · simp [term, Footprint.append]
    · intro i
      exact SupportsTerm.mono
        ((Footprint.subset_trans (Footprint.merge_contains (List.mem_ofFn.mpr ⟨i, rfl⟩)) (Footprint.subset_append_right _ _))) (arguments i) (ih i)

theorem SupportsAtom.mono {S : Core.Signature} {left right : Footprint S}
    (subset : left.Subset right) {n : Nat} {Γ : Fin n → S.S} (expression : Core.Atom S Γ) :
    SupportsAtom left expression → SupportsAtom right expression := by
  cases expression with
  | equal equality =>
      rintro ⟨lhs, rhs⟩
      exact ⟨SupportsTerm.mono subset _ lhs, SupportsTerm.mono subset _ rhs⟩
  | relation predicate arguments =>
      rintro ⟨inputs, symbol, children⟩
      exact ⟨fun i => subset.1 _ (inputs i), subset.2.2.1 _ symbol,
        fun i => SupportsTerm.mono subset _ (children i)⟩
  | row function arguments value =>
      rintro ⟨result, inputs, symbol, children, output⟩
      exact ⟨subset.1 _ result, fun i => subset.1 _ (inputs i), subset.2.2.2 _ symbol,
        (fun i => SupportsTerm.mono subset _ (children i)), SupportsTerm.mono subset _ output⟩

/-- All three atom constructors have finite support, including explicit row outputs. -/
theorem atom_supports {S : Core.Signature} {n : Nat} {Γ : Fin n → S.S}
    (expression : Core.Atom S Γ) : SupportsAtom (atom expression) expression := by
  cases expression with
  | equal equality =>
      exact ⟨SupportsTerm.mono (Footprint.subset_append_left _ _) _ (term_supports _),
        SupportsTerm.mono (Footprint.subset_append_right _ _) _ (term_supports _)⟩
  | relation predicate arguments =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · simp [atom, Footprint.append]
      · intro i
        exact SupportsTerm.mono
          ((Footprint.subset_trans (Footprint.merge_contains (List.mem_ofFn.mpr ⟨i, rfl⟩)) (Footprint.subset_append_right _ _))) _ (term_supports _)
  | row function arguments value =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [atom, Footprint.append]
      · intro i
        exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
      · simp [atom, Footprint.append]
      · intro i
        exact SupportsTerm.mono
          ((Footprint.subset_trans (Footprint.merge_contains (List.mem_ofFn.mpr ⟨i, rfl⟩)) ((Footprint.subset_trans (Footprint.subset_append_left _ _) (Footprint.subset_append_right _ _))))) _ (term_supports _)
      · exact SupportsTerm.mono
          ((Footprint.subset_trans (Footprint.subset_append_right _ _) (Footprint.subset_append_right _ _))) _ (term_supports _)

/-- Every sentence of every arbitrary Core signature has explicit finite
syntactic support, including all unused context sorts. The naming layer
constructs its local vocabulary from this support alone. -/
theorem sentence_supports {S : Core.Signature} (expression : Core.Sentence S) :
    SupportsSentence (sentence expression) expression := by
  cases expression with
  | rule rule =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · intro expression member
        exact SupportsAtom.mono
          ((Footprint.subset_trans (Footprint.merge_contains (List.mem_map.mpr ⟨expression, member, rfl⟩)) ((Footprint.subset_trans (Footprint.subset_append_left _ _) (Footprint.subset_append_right _ _))))) _ (atom_supports _)
      · exact SupportsAtom.mono
          ((Footprint.subset_trans (Footprint.subset_append_right _ _) (Footprint.subset_append_right _ _))) _ (atom_supports _)
  | query query =>
      refine ⟨?_, ?_⟩
      · intro i
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · intro expression member
        exact SupportsAtom.mono
          ((Footprint.subset_trans (Footprint.merge_contains (List.mem_map.mpr ⟨expression, member, rfl⟩)) (Footprint.subset_append_right _ _))) _ (atom_supports _)

theorem SupportsTerm.output {S : Core.Signature} (support : Footprint S)
    {n : Nat} {Γ : Fin n → S.S} {s : S.S} (expression : EQ.Term S.toSignature Γ s) :
    SupportsTerm support expression → s ∈ support.sorts := by
  refine EQ.Term.rec (motive := fun s expression =>
    SupportsTerm support expression → s ∈ support.sorts) ?_ ?_ expression
  · intro i supported
    exact supported
  · intro k w output symbol arguments ih supported
    exact supported.1

/-- Rebuild an arbitrary supported term inside the actual finite subsignature. -/
noncomputable def liftTerm {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (contextSupported : ∀ i, Γ i ∈ support.sorts) {s : S.S}
    (expression : EQ.Term S.toSignature Γ s) (supported : SupportsTerm support expression) :
    EQ.Term support.signature.toSignature (support.context Γ contextSupported)
      ⟨s, SupportsTerm.output support expression supported⟩ := by
  refine EQ.Term.rec (motive := fun s expression =>
    (supported : SupportsTerm support expression) →
      EQ.Term support.signature.toSignature (support.context Γ contextSupported)
        ⟨s, SupportsTerm.output support expression supported⟩) ?_ ?_ expression supported
  · intro i supported
    exact .var i
  · intro k w output symbol arguments ih supported
    exact @EQ.Term.app support.signature.toSignature n (support.context Γ contextSupported)
      k (fun i => ⟨w i, supported.2.1 i⟩) ⟨output, supported.1⟩
      ⟨symbol, supported.2.2.1⟩ (fun i => ih i (supported.2.2.2 i))

/-- Inclusion of a rebuilt term is the original term, with exact symbol identity. -/
theorem liftTerm_map {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (contextSupported : ∀ i, Γ i ∈ support.sorts) {s : S.S}
    (expression : EQ.Term S.toSignature Γ s) : ∀ supported : SupportsTerm support expression,
    (liftTerm support Γ contextSupported expression supported).map support.inclusion.toHom =
      expression := by
  refine EQ.Term.rec (motive := fun s expression =>
    ∀ supported : SupportsTerm support expression,
      (liftTerm support Γ contextSupported expression supported).map support.inclusion.toHom =
        expression) ?_ ?_ expression
  · intro i supported
    rfl
  · intro k w output symbol arguments ih supported
    simp only [liftTerm, EQ.Term.map]
    congr 1
    funext i
    exact ih i (supported.2.2.2 i)

/-- Equality, predicates and partial functional rows all lift without adding any
semantic restriction or replacing an ambient symbol by a fresh free one. -/
noncomputable def liftAtom {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (contextSupported : ∀ i, Γ i ∈ support.sorts)
    (expression : Core.Atom S Γ) (supported : SupportsAtom support expression) :
    Core.Atom support.signature (support.context Γ contextSupported) :=
  match expression, supported with
  | .equal equality, ⟨lhs, rhs⟩ =>
      .equal ⟨⟨equality.sort, SupportsTerm.output support equality.lhs lhs⟩,
        liftTerm support Γ contextSupported equality.lhs lhs,
        liftTerm support Γ contextSupported equality.rhs rhs⟩
  | .relation (w := w) predicate arguments, ⟨inputs, symbol, children⟩ =>
      .relation (w := fun i => ⟨w i, inputs i⟩) ⟨predicate, symbol⟩
        (fun i => liftTerm support Γ contextSupported (arguments i) (children i))
  | .row (w := w) (s := s) function arguments value, ⟨result, inputs, symbol, children, output⟩ =>
      .row (w := fun i => ⟨w i, inputs i⟩) (s := ⟨s, result⟩) ⟨function, symbol⟩
        (fun i => liftTerm support Γ contextSupported (arguments i) (children i))
        (liftTerm support Γ contextSupported value output)

theorem liftAtom_map {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (contextSupported : ∀ i, Γ i ∈ support.sorts)
    (expression : Core.Atom S Γ) (supported : SupportsAtom support expression) :
    (liftAtom support Γ contextSupported expression supported).map support.inclusion = expression := by
  cases expression <;>
    simp only [liftAtom, Core.Atom.map, Silmaril.Logic.Egg.Core.Equality.map, liftTerm_map] <;>
    rfl

noncomputable def liftAtoms {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (contextSupported : ∀ i, Γ i ∈ support.sorts)
    (atoms : List (Core.Atom S Γ)) (supported : ∀ a ∈ atoms, SupportsAtom support a) :
    List (Core.Atom support.signature (support.context Γ contextSupported)) :=
  atoms.attach.map (fun a => liftAtom support Γ contextSupported a.val (supported _ a.property))

theorem liftAtoms_map {S : Core.Signature} (support : Footprint S) {n : Nat}
    (Γ : Fin n → S.S) (contextSupported : ∀ i, Γ i ∈ support.sorts)
    (atoms : List (Core.Atom S Γ)) (supported : ∀ a ∈ atoms, SupportsAtom support a) :
    (liftAtoms support Γ contextSupported atoms supported).map (Core.Atom.map support.inclusion) =
      atoms := by
  simp only [liftAtoms, List.map_map, Function.comp_def, liftAtom_map]
  exact List.attach_map_subtype_val atoms

/-- All original rules and queries lift with their exact complete typed context. -/
noncomputable def liftSentence {S : Core.Signature} (support : Footprint S) (expression : Core.Sentence S)
    (supported : SupportsSentence support expression) : Core.Sentence support.signature :=
  match expression, supported with
  | .rule rule, ⟨context, body, head⟩ =>
      .rule ⟨rule.scope, support.context rule.context context,
        liftAtoms support rule.context context rule.body body,
        liftAtom support rule.context context rule.head head⟩
  | .query query, ⟨context, goals⟩ =>
      .query ⟨query.scope, support.context query.context context,
        liftAtoms support query.context context query.goals goals⟩

theorem liftSentence_map {S : Core.Signature} (support : Footprint S)
    (expression : Core.Sentence S) (supported : SupportsSentence support expression) :
    (liftSentence support expression supported).map support.inclusion = expression := by
  cases expression with
  | rule rule =>
      simp only [liftSentence, Core.Sentence.map, Core.Rule.map, liftAtoms_map, liftAtom_map]
      rfl
  | query query =>
      simp only [liftSentence, Core.Sentence.map, Core.Query.map, liftAtoms_map]
      rfl

/-- Every arbitrary ambient Core sentence factors exactly through an actual
finite occurrence subsignature. Naming that finite signature and composing the
local actual-byte theorem completes the arbitrary-signature representation. -/
theorem finiteSubsignatureRepresentation (S : Core.Signature) (expression : Core.Sentence S) :
    ∃ (support : Footprint S) (localSentence : Core.Sentence support.signature),
      localSentence.map support.inclusion = expression :=
  ⟨sentence expression, liftSentence _ expression (sentence_supports expression),
    liftSentence_map _ expression (sentence_supports expression)⟩

theorem Footprint.Closed.append {S : Core.Signature} {left right : Footprint S}
    (first : left.Closed) (second : right.Closed) : (left.append right).Closed := by
  refine ⟨?_, ?_, ?_⟩
  · intro symbol member
    rcases List.mem_append.mp member with original | original
    · obtain ⟨result, inputs⟩ := first.1 _ original
      exact ⟨List.mem_append_left _ result, fun i => List.mem_append_left _ (inputs i)⟩
    · obtain ⟨result, inputs⟩ := second.1 _ original
      exact ⟨List.mem_append_right _ result, fun i => List.mem_append_right _ (inputs i)⟩
  · intro symbol member i
    rcases List.mem_append.mp member with original | original
    · exact List.mem_append_left _ (first.2.1 _ original i)
    · exact List.mem_append_right _ (second.2.1 _ original i)
  · intro symbol member
    rcases List.mem_append.mp member with original | original
    · obtain ⟨result, inputs⟩ := first.2.2 _ original
      exact ⟨List.mem_append_left _ result, fun i => List.mem_append_left _ (inputs i)⟩
    · obtain ⟨result, inputs⟩ := second.2.2 _ original
      exact ⟨List.mem_append_right _ result, fun i => List.mem_append_right _ (inputs i)⟩

theorem Footprint.Closed.merge {S : Core.Signature} (entries : List (Footprint S))
    (closed : ∀ entry ∈ entries, entry.Closed) : (Footprint.merge entries).Closed := by
  induction entries with
  | nil => simp [Footprint.merge, Footprint.empty, Footprint.Closed]
  | cons first rest ih =>
      exact (closed first (by simp)).append (ih (fun entry member => closed entry (by simp [member])))

theorem term_closed {S : Core.Signature} {n : Nat} {Γ : Fin n → S.S} {s : S.S}
    (expression : EQ.Term S.toSignature Γ s) : (term expression).Closed := by
  refine EQ.Term.rec (motive := fun _ expression => (term expression).Closed) ?_ ?_ expression
  · intro i
    simp [term, Footprint.Closed]
  · intro k w output symbol arguments ih
    apply Footprint.Closed.append
    · refine ⟨?_, ?_, ?_⟩
      · intro packed member
        cases List.mem_singleton.mp member
        exact ⟨List.mem_cons_self, fun i => List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)⟩
      · intro _ member
        cases member
      · intro _ member
        cases member
    · exact Footprint.Closed.merge _ (fun entry member => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
        exact ih i)

theorem atom_closed {S : Core.Signature} {n : Nat} {Γ : Fin n → S.S}
    (expression : Core.Atom S Γ) : (atom expression).Closed := by
  cases expression with
  | equal equality => exact (term_closed _).append (term_closed _)
  | relation predicate arguments =>
      apply Footprint.Closed.append
      · refine ⟨?_, ?_, ?_⟩
        · intro _ member; cases member
        · intro packed member i
          cases List.mem_singleton.mp member
          exact List.mem_ofFn.mpr ⟨i, rfl⟩
        · intro _ member; cases member
      · exact Footprint.Closed.merge _ (fun entry member => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
          exact term_closed (arguments i))
  | row function arguments value =>
      apply Footprint.Closed.append
      · refine ⟨?_, ?_, ?_⟩
        · intro _ member; cases member
        · intro _ member; cases member
        · intro packed member
          cases List.mem_singleton.mp member
          exact ⟨List.mem_cons_self, fun i => List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)⟩
      · exact (Footprint.Closed.merge _ (fun entry member => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
          exact term_closed (arguments i))).append (term_closed value)

/-- The whole finite occurrence signature has every input/output sort needed by
its declared symbols, as well as the complete separate scoped context. -/
theorem sentence_closed {S : Core.Signature} (expression : Core.Sentence S) :
    (sentence expression).Closed := by
  have contextClosed (sorts : List S.S) : (⟨sorts, [], [], []⟩ : Footprint S).Closed := by
    simp [Footprint.Closed]
  cases expression with
  | rule rule =>
      exact (contextClosed _).append
        ((Footprint.Closed.merge _ (fun entry member => by
          obtain ⟨atom, _, rfl⟩ := List.mem_map.mp member
          exact atom_closed atom)).append (atom_closed rule.head))
  | query query =>
      exact (contextClosed _).append (Footprint.Closed.merge _ (fun entry member => by
        obtain ⟨atom, _, rfl⟩ := List.mem_map.mp member
        exact atom_closed atom))

end Silmaril.Logic.Egglog.Source.Named.FiniteSupport
