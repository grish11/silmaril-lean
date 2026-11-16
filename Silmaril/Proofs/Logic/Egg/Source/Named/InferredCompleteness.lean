module

public import Silmaril.Logic.Egg.Source.Named.Inference.Thms
public import Silmaril.Logic.Egg.Source.Named.Representation.Defs
public import Silmaril.Logic.Egg.Source.Named.Representation.Support.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named (constructor?_complete sequence_component sequence_complete termAt?)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Inference supplies every profile needed by resolution. The vocabulary may
be exactly the inferred one or any actual checked vocabulary containing support. -/
theorem inferTerm_resolve {D : Declarations} (Γ : CheckedContext D) (raw : RawTerm)
    (result : String) (support : Support)
    (inferred : raw.infer? Γ.bindings = some (result, support)) (within : support.Within D) :
    ∃ packed : PackedTerm Γ, resolveTerm? Γ raw = some packed ∧ packed.1.val = result := by
  induction raw generalizing result support with
  | var name =>
      cases found : Γ.bindings.find? (fun b => b.name == name) with
      | none => simp [RawTerm.infer?, found] at inferred
      | some binding =>
          simp only [RawTerm.infer?, found, bind, Option.bind, Option.pure_def,
            Option.some.injEq] at inferred
          cases inferred
          have member := List.mem_of_find?_eq_some found
          obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
          have named : (Γ.bindings.get index).name = name := by
            rw [equal]
            simpa using List.find?_some found
          refine ⟨⟨Γ.profile index, .var index⟩, ?_, ?_⟩
          · simpa only [eraseTerm, named] using eraseTerm_resolve Γ (.var index)
          · change (Γ.bindings.get index).sort = binding.sort
            rw [equal]
  | app name annotation n arguments ih =>
      cases sequence : Silmaril.Logic.Egglog.Source.Named.sequence? n
          (fun i => (arguments i).infer? Γ.bindings) with
      | none => simp [RawTerm.infer?, sequence] at inferred
      | some children =>
          simp only [RawTerm.infer?, sequence, bind, Option.bind, Option.pure_def,
            Option.some.injEq] at inferred
          cases inferred
          have childWithin (i : Fin n) : (children i).2.Within D := by
            constructor
            · intro s member
              apply within.1 s
              apply List.mem_cons_of_mem
              exact Support.sorts_mem_concat _ (children i).2
                (List.mem_ofFn.mpr ⟨i, rfl⟩) s member
            · intro o member
              apply within.2 o
              apply List.mem_cons_of_mem
              have concatMember : o ∈ (Support.concat
                  (List.ofFn (fun j => (children j).2))).constructors := by
                have helper : ∀ (xs : List Support) (x : Support), x ∈ xs →
                    ∀ o ∈ x.constructors, o ∈ (Support.concat xs).constructors := by
                  intro xs
                  induction xs with
                  | nil => intro _ h; cases h
                  | cons first rest next =>
                      intro x hx o ho
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact List.mem_append_left _ ho
                      · exact List.mem_append_right _ (next x hx o ho)
                exact helper _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩) o member
              exact concatMember
          choose packed compiled outputs using (fun i =>
            ih i (children i).1 (children i).2
              (sequence_component n _ children sequence i) (childWithin i))
          let output : D.checked.LocalSort := ⟨annotation, within.1 annotation (by simp)⟩
          let declaration : Silmaril.Logic.Egglog.Source.Named.TotalDeclaration :=
            ⟨name, List.ofFn (fun i => (children i).1), annotation⟩
          let operation : D.signature.Op n (fun i => (packed i).1) output :=
            ⟨declaration, within.2 declaration (by simp [declaration]), by
              change List.ofFn (fun i => (children i).1) = List.ofFn (fun i => (packed i).1.val)
              congr 1
              funext i
              exact (outputs i).symm, rfl⟩
          have argumentsComplete : (fun i => do
              let value ← resolveTerm? Γ (arguments i)
              termAt? ((packed i).1) value) = (fun i => some (packed i).2) := by
            funext i
            simp [compiled i, termAt?]
          refine ⟨⟨output, .app operation (fun i => (packed i).2)⟩, ?_, rfl⟩
          change resolveTerm? Γ (.app operation.val.name output.val n arguments) = _
          simp only [resolveTerm?, constructor?_complete, ↓reduceIte, bind, Option.bind]
          simp only [bind, Option.bind] at argumentsComplete
          rw [argumentsComplete, sequence_complete]
          rfl

namespace Support

theorem within_left {D : Declarations} (a b : Support) (h : (a.append b).Within D) :
    a.Within D :=
  ⟨fun s hs => h.1 s (List.mem_append_left _ hs),
    fun o ho => h.2 o (List.mem_append_left _ ho)⟩

theorem within_right {D : Declarations} (a b : Support) (h : (a.append b).Within D) :
    b.Within D :=
  ⟨fun s hs => h.1 s (List.mem_append_right _ hs),
    fun o ho => h.2 o (List.mem_append_right _ ho)⟩

theorem within_concat_member {D : Declarations} (xs : List Support)
    (h : (concat xs).Within D) (x : Support) (member : x ∈ xs) : x.Within D := by
  induction xs with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · rw [equal]
        exact within_left first (concat rest) h
      · exact ih (within_right first (concat rest) h) member
end Support

theorem inferEquality_resolve {D : Declarations} (Γ : CheckedContext D)
    (raw : RawEquality) (support : Support)
    (inferred : raw.support? Γ.bindings = some support) (within : support.Within D) :
    ∃ typed, resolveEquality? Γ raw = some typed := by
  cases hl : raw.left.infer? Γ.bindings with
  | none => simp [RawEquality.support?, hl] at inferred
  | some left =>
      cases hr : raw.right.infer? Γ.bindings with
      | none => simp [RawEquality.support?, hl, hr] at inferred
      | some right =>
          by_cases same : left.1 = right.1
          · simp only [RawEquality.support?, hl, hr, same, ↓reduceIte, bind, Option.bind,
              Option.pure_def, Option.some.injEq] at inferred
            subst support
            obtain ⟨⟨s, lhs⟩, hleft, leftOutput⟩ := inferTerm_resolve Γ raw.left left.1 left.2 hl
              (Support.within_left _ _ within)
            obtain ⟨⟨t, rhs⟩, hright, rightOutput⟩ := inferTerm_resolve Γ raw.right right.1 right.2 hr
              (Support.within_right _ _ within)
            have outputs : t = s := Subtype.ext (rightOutput.trans (same.symm.trans leftOutput.symm))
            subst t
            exact ⟨⟨s, lhs, rhs⟩, by simp [resolveEquality?, hleft, hright, termAt?]⟩
          · simp [RawEquality.support?, hl, hr, same] at inferred

theorem inferRule_resolve {D : Declarations} (raw : RawRule) (support : Support)
    (inferred : raw.support? = some support) (within : support.Within D)
    (unique : (raw.context.map Silmaril.Logic.Egglog.Source.Named.Binding.name).Nodup)
    (legal : ∀ b ∈ raw.context, Silmaril.Logic.Egglog.Source.Named.LegalName b.name) :
    ∃ typed, resolveRule? D raw = some typed := by
  cases hg : raw.guards.mapM (RawEquality.support? raw.context) with
  | none => simp [RawRule.support?, hg] at inferred
  | some guardSupports =>
      cases hh : raw.conclusion.support? raw.context with
      | none => simp [RawRule.support?, hg, hh] at inferred
      | some conclusionSupport =>
          simp only [RawRule.support?, hg, hh, bind, Option.bind, Option.pure_def,
            Option.some.injEq] at inferred
          subst support
          let Γ : CheckedContext D :=
            ⟨raw.context, unique, fun i => within.1 (raw.context.get i).sort
              (List.mem_append_left _ (List.mem_map.mpr ⟨raw.context.get i, List.get_mem _ _, rfl⟩))⟩
          have all : ∀ e ∈ raw.guards, ∃ typed, resolveEquality? Γ e = some typed ∧ True := by
            intro e member
            obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
            have entry := Silmaril.Logic.Egglog.Source.Named.mapM_get _ _ _ hg index
            obtain ⟨typed, success⟩ := inferEquality_resolve Γ _ _ entry
              (Support.within_concat_member guardSupports
                (Support.within_left _ _ (Support.within_right _ _ within)) _ (List.get_mem _ _))
            exact ⟨typed, success, trivial⟩
          obtain ⟨guards, hguards, _⟩ := mapM_exists_property (resolveEquality? Γ)
            (fun _ => True) raw.guards all
          obtain ⟨conclusion, hconclusion⟩ := inferEquality_resolve Γ raw.conclusion _ hh
            (Support.within_right _ _ (Support.within_right _ _ within))
          refine ⟨⟨Γ.bindings.length, Γ.profile, guards, conclusion⟩, ?_⟩
          have context : Silmaril.Logic.Egglog.Source.Named.Context.check D.checked raw.context = some Γ :=
            Silmaril.Logic.Egglog.Source.Named.CheckedContext.check_self Γ legal
          simp only [resolveRule?, context, bind, Option.bind, hguards, hconclusion, Option.pure_def]

/-- Source context checks used below come from the actual successful supplied
resolver. They are not imposed as new assumptions on accepted programs. -/
theorem resolveRule_context_valid {D : Declarations} (raw : RawRule)
    (typed : Core.Rule D.signature) (resolved : resolveRule? D raw = some typed) :
    Silmaril.Logic.Egglog.Source.Named.Context.Valid D.checked raw.context := by
  cases hc : Silmaril.Logic.Egglog.Source.Named.Context.check D.checked raw.context with
  | none => simp [resolveRule?, hc] at resolved
  | some Γ => exact Silmaril.Logic.Egglog.Source.Named.context_check_valid D.checked raw.context Γ hc

theorem Support.within_checked {D : Declarations} (support : Support)
    (within : support.Within D) (closed : support.Closed) :
    support.Within (support.checked within closed) := by
  constructor <;> intro x member <;> simpa [Support.checked, Support.data] using member

/-- General same-original-byte inferred admission, proved by actual support
collection and actual target resolution. No replacement bytes are written. -/
theorem inferredAdmissionComplete_task : Task.inferredAdmissionComplete := by
  intro D p
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
  let E := support.checked within closed
  let interpretation := support.interpretation within closed
  have inferred : inferDeclarations? p.raw = some E := by
    simp only [inferDeclarations?, hs, bind, Option.bind]
    change (if h : support.data.Valid then some (⟨⟨support.data, h⟩, rfl, rfl⟩ : Declarations)
      else none) = some E
    rw [dite_eq_left (support.data_valid within closed)]
    rfl
  have labels : (p.raw.map RawRule.name).Nodup ∧
      ∀ r ∈ p.raw, Silmaril.Logic.Egglog.Source.Named.LegalName r.name := by
    have success := p.resolve_eq
    unfold resolveProgram? at success
    split at success
    · assumption
    · contradiction
  have all : ∀ r ∈ p.raw, ∃ typed, resolveRule? E r = some typed ∧ True := by
    intro r member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    have entry := Silmaril.Logic.Egglog.Source.Named.mapM_get _ _ _ hs index
    have original := Silmaril.Logic.Egglog.Source.Named.mapM_get _ _ _ p.mapM_eq index
    have context := resolveRule_context_valid _ _ original
    have contained : (supports.get (Fin.cast
        (Silmaril.Logic.Egglog.Source.Named.mapM_length _ _ _ hs) index)).Within E :=
      Support.within_concat_member supports (support.within_checked within closed) _ (List.get_mem _ _)
    obtain ⟨typed, accepted⟩ := inferRule_resolve _ _ entry contained context.1 context.2.1
    exact ⟨typed, accepted, trivial⟩
  obtain ⟨rules, compiled, _⟩ := mapM_exists_property (resolveRule? E) (fun _ => True) p.raw all
  have accepted : resolveProgram? E p.raw = some rules := by
    simp only [resolveProgram?, ite_eq_left labels, compiled]
  let q : AcceptedProgram E := ⟨p.bytes, p.raw, p.read_eq, rules, accepted⟩
  have mapped := DeclarationHom.resolveProgram_map interpretation p.raw rules accepted
  have exactRules : rules.map (Core.Rule.map interpretation.symbols.toHom) = p.resolved :=
    Option.some.inj (mapped.symm.trans p.resolve_eq)
  exact ⟨⟨E, q, inferred⟩, interpretation.symbols.toHom, rfl, rfl, exactRules⟩

/-- Every arbitrary finite ordered ambient rule file has actual accepted complete
inferred bytes. This discharges the anti-subset completion gate unconditionally. -/
theorem finiteProgramRepresentation_task : Task.finiteProgramRepresentation := by
  intro S rules
  obtain ⟨D, p, symbols, represented⟩ :=
    FiniteSupport.finiteSuppliedProgramRepresentation S rules
  obtain ⟨q, interpretation, _, _, exactRules⟩ := inferredAdmissionComplete_task D p
  refine ⟨q, interpretation ≫ symbols, ?_⟩
  have composition : q.program.resolved.map (Core.Rule.map (interpretation ≫ symbols)) =
      (q.program.resolved.map (Core.Rule.map interpretation)).map (Core.Rule.map symbols) := by
    rw [List.map_map]
    apply congrArg (fun f => q.program.resolved.map f)
    funext r
    exact Core.Rule.map_comp interpretation symbols r
  rw [composition, exactRules, represented]

end Silmaril.Logic.Egg.Source.Named
