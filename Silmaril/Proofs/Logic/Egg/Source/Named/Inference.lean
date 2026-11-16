module

public import Silmaril.Logic.Egg.Source.Named.Supplied.Thms
public import Mathlib.Data.List.Nodup

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named (Binding TotalDeclaration constructor_name_injective)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every collected occurrence belongs to the actual supplied vocabulary. -/
def Support.Within (support : Support) (D : Declarations) : Prop :=
  (∀ s ∈ support.sorts, s ∈ D.checked.data.sorts) ∧
  ∀ o ∈ support.constructors, o ∈ D.checked.data.constructors

/-- Profiles are closed inside collected support itself, rather than merely
being well-formed in a larger supplied vocabulary. -/
def Support.Closed (support : Support) : Prop :=
  ∀ o ∈ support.constructors,
    (∀ s ∈ o.inputs, s ∈ support.sorts) ∧ o.output ∈ support.sorts

namespace Support

theorem within_append {D : Declarations} {a b : Support}
    (ha : a.Within D) (hb : b.Within D) : (a.append b).Within D := by
  constructor
  · intro s member
    rcases List.mem_append.mp member with member | member
    · exact ha.1 s member
    · exact hb.1 s member
  · intro o member
    rcases List.mem_append.mp member with member | member
    · exact ha.2 o member
    · exact hb.2 o member

theorem closed_append {a b : Support} (ha : a.Closed) (hb : b.Closed) :
    (a.append b).Closed := by
  intro o member
  rcases List.mem_append.mp member with member | member
  · exact ⟨fun s hs => List.mem_append_left _ ((ha o member).1 s hs),
      List.mem_append_left _ (ha o member).2⟩
  · exact ⟨fun s hs => List.mem_append_right _ ((hb o member).1 s hs),
      List.mem_append_right _ (hb o member).2⟩

theorem concat_within {D : Declarations} (xs : List Support)
    (h : ∀ x ∈ xs, x.Within D) : (concat xs).Within D := by
  induction xs with
  | nil =>
      constructor <;> intro _ member <;> cases member
  | cons first rest ih =>
      exact within_append (h first (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem concat_closed (xs : List Support) (h : ∀ x ∈ xs, x.Closed) : (concat xs).Closed := by
  induction xs with
  | nil => intro _ h; cases h
  | cons first rest ih =>
      exact closed_append (h first (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem sorts_mem_concat (xs : List Support) (x : Support) (hx : x ∈ xs)
    (s : String) (hs : s ∈ x.sorts) : s ∈ (concat xs).sorts := by
  induction xs with
  | nil => cases hx
  | cons first rest ih =>
      rcases List.mem_cons.mp hx with rfl | member
      · exact List.mem_append_left _ hs
      · exact List.mem_append_right _ (ih member)
end Support

/-- Unique explicit binders make the independent profile inference lookup exact. -/
theorem infer_variable_lookup {D : Declarations} (Γ : CheckedContext D)
    (i : Fin Γ.bindings.length) :
    Γ.bindings.find? (fun b => b.name == (Γ.bindings.get i).name) = some (Γ.bindings.get i) := by
  cases found : Γ.bindings.find? (fun b => b.name == (Γ.bindings.get i).name) with
  | none =>
      have absent := List.find?_eq_none.mp found (Γ.bindings.get i) (List.get_mem _ _)
      simp at absent
  | some binding =>
      have member := List.mem_of_find?_eq_some found
      have same : binding.name = (Γ.bindings.get i).name := by
        simpa using List.find?_some found
      have equal := List.inj_on_of_nodup_map Γ.unique member (List.get_mem _ _) same
      subst binding
      rfl

/-- Typed erasure infers its actual result sort, with all constructor profiles
closed in the collected support and present in the original vocabulary. -/
theorem eraseTerm_infer {D : Declarations} (Γ : CheckedContext D) {s : D.checked.LocalSort}
    (term : EQ.Term D.signature Γ.profile s) :
    ∃ support : Support, (eraseTerm Γ term).infer? Γ.bindings = some (s.val, support) ∧
      support.Within D ∧ support.Closed ∧ s.val ∈ support.sorts := by
  refine EQ.Term.rec (motive := fun s term => ∃ support : Support,
    (eraseTerm Γ term).infer? Γ.bindings = some (s.val, support) ∧
      support.Within D ∧ support.Closed ∧ s.val ∈ support.sorts) ?_ ?_ term
  · intro i
    refine ⟨⟨[(Γ.profile i).val], []⟩, ?_, ?_, ?_, by simp⟩
    · simp only [eraseTerm, RawTerm.infer?, infer_variable_lookup Γ i, bind, Option.bind, Option.pure_def]
      rfl
    · exact ⟨fun _ member => (List.mem_singleton.mp member) ▸ (Γ.profile i).property,
        fun _ member => by cases member⟩
    · intro _ member; cases member
  · intro n w s o arguments ih
    classical
    choose supports success within closed output using ih
    let children : Support := Support.concat (List.ofFn supports)
    let declaration : TotalDeclaration := ⟨o.val.name, List.ofFn (fun i => (w i).val), s.val⟩
    have declaration_eq : declaration = o.val := by
      rcases o with ⟨⟨name, inputs, result⟩, member, inputsEq, outputEq⟩
      simp only [declaration] at *
      cases inputsEq
      cases outputEq
      rfl
    let support : Support := ⟨s.val :: children.sorts, declaration :: children.constructors⟩
    refine ⟨support, ?_, ?_, ?_, by simp [support]⟩
    · have sequence : Silmaril.Logic.Egglog.Source.Named.sequence? n
          (fun i => (eraseTerm Γ (arguments i)).infer? Γ.bindings) =
          some (fun i => ((w i).val, supports i)) := by
        have pointwise : (fun i => (eraseTerm Γ (arguments i)).infer? Γ.bindings) =
            (fun i => some ((w i).val, supports i)) := funext success
        rw [pointwise, Silmaril.Logic.Egglog.Source.Named.sequence_complete]
      simp only [eraseTerm, RawTerm.infer?, sequence, bind, Option.bind, Option.pure_def]
      rfl
    · have childrenWithin := Support.concat_within (List.ofFn supports) (by
        intro x member
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
        exact within i)
      constructor
      · intro name member
        rcases List.mem_cons.mp member with rfl | member
        · exact s.property
        · exact childrenWithin.1 name member
      · intro symbol member
        rcases List.mem_cons.mp member with rfl | member
        · rw [declaration_eq]
          exact o.property.1
        · exact childrenWithin.2 symbol member
    · have childrenClosed := Support.concat_closed (List.ofFn supports) (by
        intro x member
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
        exact closed i)
      intro symbol member
      rcases List.mem_cons.mp member with rfl | member
      · constructor
        · intro name member
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
          apply List.mem_cons_of_mem
          exact Support.sorts_mem_concat _ (supports i) (List.mem_ofFn.mpr ⟨i, rfl⟩) _ (output i)
        · exact List.mem_cons_self
      · exact ⟨fun name member' => List.mem_cons_of_mem _ ((childrenClosed symbol member).1 name member'),
          List.mem_cons_of_mem _ (childrenClosed symbol member).2⟩

namespace Support

/-- Normalization removes only repeated identical profiles; conflicting
same-name profiles remain visible to validity checking. -/
def data (support : Support) : Silmaril.Logic.Egglog.Source.Named.DeclarationData :=
  ⟨support.sorts.eraseDups, support.constructors.eraseDups, [], []⟩

/-- The executable first-occurrence deduplicator retains a duplicate-free list. -/
theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  have result : ∀ n, ∀ ys : List α, ys.length = n → ys.eraseDups.Nodup := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
        intro ys length
        cases ys with
        | nil => simp
        | cons first rest =>
            rw [List.eraseDups_cons]
            apply List.nodup_cons.mpr
            constructor
            · intro member
              have impossible := (List.mem_filter.mp (List.mem_eraseDups.mp member)).2
              simp at impossible
            · apply ih (rest.filter (fun x => !(x == first))).length
              · have bound := List.length_filter_le (fun x => !(x == first)) rest
                simp only [List.length_cons] at length
                omega
              · rfl
  exact result xs.length xs rfl

theorem data_valid {D : Declarations} (support : Support) (within : support.Within D)
    (closed : support.Closed) : support.data.Valid := by
  refine ⟨eraseDups_nodup support.sorts, ?_, ?_, ?_, ?_⟩
  · simp only [data, List.map_nil, List.append_nil]
    apply List.Nodup.map_on
    · intro x hx y hy equal
      exact constructor_name_injective D.checked
        (within.2 x (by simpa using hx)) (within.2 y (by simpa using hy)) equal
    · exact eraseDups_nodup support.constructors
  · intro name member
    exact D.checked.valid.2.2.1 name (within.1 name (by simpa [data] using member))
  · intro o member
    have original : o ∈ support.constructors := by simpa [data] using member
    have named := D.checked.valid.2.2.2.1 o (List.mem_append_left _ (within.2 o original))
    exact ⟨named.1, fun name member => by simpa [data] using (closed o original).1 name member,
      by simpa [data] using (closed o original).2⟩
  · intro _ member
    cases member

/-- This is exactly the data used by executable inference. -/
def checked {D : Declarations} (support : Support) (within : support.Within D)
    (closed : support.Closed) : Declarations :=
  ⟨⟨support.data, support.data_valid within closed⟩, rfl, rfl⟩

/-- Inferred names map to their actual supplied meanings, not free operations. -/
def interpretation {D : Declarations} (support : Support) (within : support.Within D)
    (closed : support.Closed) : DeclarationHom (support.checked within closed) D where
  symbols :=
    { sorts := fun s => ⟨s.val, within.1 s.val (by simpa [checked, data] using s.property)⟩
      ops := fun o => ⟨o.val, within.2 o.val (by simpa [checked, data] using o.property.1),
        o.property.2.1, o.property.2.2⟩
      rels := fun r => False.elim (by simpa [checked, data] using r.property.1)
      functions := fun f => False.elim (by simpa [checked, data] using f.property.1) }
  sort_name := fun _ => rfl
  constructor_name := fun _ => rfl
  relation_name := fun r => False.elim (by simpa [checked, data] using r.property.1)
  function_name := fun f => False.elim (by simpa [checked, data] using f.property.1)
end Support

/-- Finite traversal existence with a real output invariant. -/
theorem mapM_exists_property {α β : Type} (f : α → Option β) (P : β → Prop)
    (xs : List α) (good : ∀ x ∈ xs, ∃ y, f x = some y ∧ P y) :
    ∃ ys, xs.mapM f = some ys ∧ ∀ y ∈ ys, P y := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons first rest ih =>
      obtain ⟨y, hy, py⟩ := good first (by simp)
      obtain ⟨ys, hys, pys⟩ := ih (fun x member => good x (by simp [member]))
      exact ⟨y :: ys, by simp [hy, hys], by simpa using And.intro py pys⟩

theorem resolveEquality_support {D : Declarations} (Γ : CheckedContext D)
    (raw : RawEquality) (typed : Core.Equality D.signature Γ.profile)
    (resolved : resolveEquality? Γ raw = some typed) :
    ∃ support, raw.support? Γ.bindings = some support ∧ support.Within D ∧ support.Closed := by
  rw [← resolveEquality_erase Γ raw typed resolved]
  obtain ⟨left, hl, hwl, hcl, _⟩ := eraseTerm_infer Γ typed.lhs
  obtain ⟨right, hr, hwr, hcr, _⟩ := eraseTerm_infer Γ typed.rhs
  exact ⟨left.append right, by simp [eraseEquality, RawEquality.support?, hl, hr],
    Support.within_append hwl hwr, Support.closed_append hcl hcr⟩

theorem resolveRule_support {D : Declarations} (raw : RawRule) (typed : Core.Rule D.signature)
    (resolved : resolveRule? D raw = some typed) :
    ∃ support, raw.support? = some support ∧ support.Within D ∧ support.Closed := by
  cases hc : Silmaril.Logic.Egglog.Source.Named.Context.check D.checked raw.context with
  | none => simp [resolveRule?, hc] at resolved
  | some Γ =>
      cases hg : raw.guards.mapM (resolveEquality? Γ) with
      | none => simp [resolveRule?, hc, hg] at resolved
      | some guards =>
          cases hh : resolveEquality? Γ raw.conclusion with
          | none => simp [resolveRule?, hc, hg, hh] at resolved
          | some conclusion =>
              have bindings := Silmaril.Logic.Egglog.Source.Named.context_check_bindings
                D.checked raw.context Γ hc
              have good : ∀ e ∈ raw.guards, ∃ support,
                  e.support? raw.context = some support ∧ support.Within D ∧ support.Closed := by
                intro e member
                obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
                have entry := Silmaril.Logic.Egglog.Source.Named.mapM_get _ _ _ hg index
                simpa only [bindings] using resolveEquality_support Γ _ _ entry
              obtain ⟨supports, hs, properties⟩ := mapM_exists_property
                (RawEquality.support? raw.context)
                (fun support => support.Within D ∧ support.Closed) raw.guards good
              obtain ⟨last, hl, hwl, hcl⟩ := resolveEquality_support Γ raw.conclusion conclusion hh
              have contextWithin : (⟨raw.context.map Binding.sort, []⟩ : Support).Within D := by
                constructor
                · intro name member
                  obtain ⟨binding, bindingMember, named⟩ := List.mem_map.mp member
                  rw [← named]
                  exact (Silmaril.Logic.Egglog.Source.Named.context_check_valid
                    D.checked raw.context Γ hc).2.2 binding bindingMember
                · intro _ member; cases member
              have contextClosed : (⟨raw.context.map Binding.sort, []⟩ : Support).Closed := by
                intro _ member; cases member
              have lastRaw : raw.conclusion.support? raw.context = some last := by
                simpa only [bindings] using hl
              refine ⟨(⟨raw.context.map Binding.sort, []⟩ : Support).append
                ((Support.concat supports).append last), ?_, ?_, ?_⟩
              · simp only [RawRule.support?, hs, lastRaw, bind, Option.bind, Option.pure_def]
              · exact Support.within_append contextWithin
                  (Support.within_append
                    (Support.concat_within supports (fun x member => (properties x member).1)) hwl)
              · exact Support.closed_append contextClosed
                  (Support.closed_append
                    (Support.concat_closed supports (fun x member => (properties x member).2)) hcl)

/-- Every actual supplied admission successfully computes a closed inferred
vocabulary, retaining the source occurrence profiles and all unused binders. -/
theorem inferDeclarations_exists {D : Declarations} (p : AcceptedProgram D) :
    ∃ E : Declarations, inferDeclarations? p.raw = some E := by
  have good : ∀ r ∈ p.raw, ∃ support,
      r.support? = some support ∧ support.Within D ∧ support.Closed := by
    intro r member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact resolveRule_support _ _
      (Silmaril.Logic.Egglog.Source.Named.mapM_get _ _ _ p.mapM_eq index)
  obtain ⟨supports, hs, properties⟩ := mapM_exists_property RawRule.support?
    (fun support => support.Within D ∧ support.Closed) p.raw good
  let support := Support.concat supports
  have within : support.Within D :=
    Support.concat_within supports (fun x member => (properties x member).1)
  have closed : support.Closed :=
    Support.concat_closed supports (fun x member => (properties x member).2)
  refine ⟨support.checked within closed, ?_⟩
  simp only [inferDeclarations?, hs, bind, Option.bind]
  change (if h : support.data.Valid then some (⟨⟨support.data, h⟩, rfl, rfl⟩ : Declarations)
    else none) = some (support.checked within closed)
  rw [dite_eq_left (support.data_valid within closed)]
  rfl

end Silmaril.Logic.Egg.Source.Named
