module

public import Silmaril.Logic.Egg.Source.Named.Representation.Bytes.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Support.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Naming.Thms
public import Silmaril.Logic.Egglog.Core.Egg.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.FiniteSupport
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named.FiniteSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Monotonicity of complete sentence support, including unused binders. -/
theorem supportsSentence_mono {S : Silmaril.Logic.Egglog.Core.Signature}
    {left right : Footprint S} (subset : left.Subset right)
    (r : Silmaril.Logic.Egglog.Core.Sentence S) (supported : SupportsSentence left r) :
    SupportsSentence right r := by
  cases r with
  | rule r =>
      exact ⟨fun i => subset.1 _ (supported.1 i),
        fun a member => SupportsAtom.mono subset a (supported.2.1 a member),
        SupportsAtom.mono subset _ supported.2.2⟩
  | query q =>
      exact ⟨fun i => subset.1 _ (supported.1 i),
        fun a member => SupportsAtom.mono subset a (supported.2 a member)⟩

/-- One finite occurrence signature for the whole ordered file. -/
def program (S : Core.Signature) (rules : List (Core.Rule S)) :
    Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S) :=
  Footprint.merge (rules.map (fun r => sentence (Silmaril.Logic.Egglog.Core.Egg.sentence r)))

theorem program_closed (S : Core.Signature) (rules : List (Core.Rule S)) :
    (program S rules).Closed :=
  Footprint.Closed.merge _ (by
    intro entry member
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
    exact sentence_closed _)

theorem program_supports (S : Core.Signature) (rules : List (Core.Rule S))
    (r : Core.Rule S) (member : r ∈ rules) :
    SupportsSentence (program S rules) (Silmaril.Logic.Egglog.Core.Egg.sentence r) :=
  supportsSentence_mono (Footprint.merge_contains (List.mem_map.mpr ⟨r, member, rfl⟩))
    _ (sentence_supports _)

noncomputable def liftEquality {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S))
    {n : Nat} (Γ : Fin n → S.S) (context : ∀ i, Γ i ∈ support.sorts)
    (e : Core.Equality S Γ)
    (supported : SupportsAtom support (Silmaril.Logic.Egglog.Core.Egg.atom e)) :
    Core.Equality support.signature.toSignature (support.context Γ context) :=
  ⟨⟨e.sort, SupportsTerm.output support e.lhs supported.1⟩,
    liftTerm support Γ context e.lhs supported.1,
    liftTerm support Γ context e.rhs supported.2⟩

theorem liftEquality_map {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S))
    {n : Nat} (Γ : Fin n → S.S) (context : ∀ i, Γ i ∈ support.sorts)
    (e : Core.Equality S Γ)
    (supported : SupportsAtom support (Silmaril.Logic.Egglog.Core.Egg.atom e)) :
    (liftEquality support Γ context e supported).map support.inclusion.toHom = e := by
  simp only [liftEquality, Core.Equality.map, liftTerm_map]
  rfl

noncomputable def liftRule {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S)) (r : Core.Rule S)
    (supported : SupportsSentence support (Silmaril.Logic.Egglog.Core.Egg.sentence r)) :
    Core.Rule support.signature.toSignature where
  scope := r.scope
  context := support.context r.context supported.1
  guards := r.guards.attach.map (fun e => liftEquality support r.context supported.1 e.val
    (supported.2.1 _ (List.mem_map.mpr ⟨e.val, e.property, rfl⟩)))
  conclusion := liftEquality support r.context supported.1 r.conclusion supported.2.2

theorem liftRule_map {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S)) (r : Core.Rule S)
    (supported : SupportsSentence support (Silmaril.Logic.Egglog.Core.Egg.sentence r)) :
    (liftRule support r supported).map support.inclusion.toHom = r := by
  have guards : ((liftRule support r supported).guards).map
      (Core.Equality.map support.inclusion.toHom) = r.guards := by
    simp only [liftRule, List.map_map, Function.comp_def, liftEquality_map]
    exact List.attach_map_subtype_val r.guards
  cases r
  simp only [Core.Rule.map, liftRule, liftEquality_map] at guards ⊢
  rw [guards]
  rfl

/-- Table/predicate packets are impossible in the constructor-only ambient
signature. No unsupported symbol kinds are silently discarded. -/
theorem relations_empty {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S)) : support.relations = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r _
  exact r.2.2.elim

theorem functions_empty {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S)) : support.functions = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro f _
  exact f.2.2.2.elim

noncomputable def declarations {S : Core.Signature}
    (support : Footprint (Silmaril.Logic.Egglog.Core.Egg.signature S)) (closed : support.Closed) :
    Declarations where
  checked := support.declarations closed
  noRelations := by simp [Footprint.declarations, Footprint.declarationData, relations_empty]
  noFunctions := by simp [Footprint.declarations, Footprint.declarationData, functions_empty]

/-- Arbitrary ambient signatures and arbitrary finite guarded-rule files factor
through one checked finite named constructor signature, with exact list equality. -/
theorem finiteNamedProgramRepresentation (S : Core.Signature) (rules : List (Core.Rule S)) :
    ∃ (D : Declarations) (localRules : List (Core.Rule D.signature)) (symbols : D.signature ⟶ S),
      localRules.map (Core.Rule.map symbols) = rules := by
  classical
  let support := program S rules
  let closed := program_closed S rules
  let D := declarations support closed
  let localRules := rules.attach.map (fun r => liftRule support r.val (program_supports S rules r.val r.property))
  let encoded := localRules.map (Core.Rule.map (support.encode closed).toHom)
  refine ⟨D, encoded, (support.decode closed ≫ support.inclusion).toHom, ?_⟩
  change (localRules.map (Core.Rule.map (support.encode closed).toHom)).map
    (Core.Rule.map (support.decode closed ≫ support.inclusion).toHom) = rules
  have one (r : Core.Rule support.signature.toSignature) :
      (r.map (support.encode closed).toHom).map
        (support.decode closed ≫ support.inclusion).toHom = r.map support.inclusion.toHom := by
    have hom : (support.encode closed ≫ support.decode closed ≫ support.inclusion).toHom =
        support.inclusion.toHom := by
      rw [← Category.assoc, support.encode_decode closed]
      rfl
    rw [← Core.Rule.map_comp]
    change r.map (support.encode closed ≫ support.decode closed ≫ support.inclusion).toHom = _
    rw [hom]
  simp only [List.map_map, Function.comp_def, one, localRules, liftRule_map]
  exact List.attach_map_subtype_val rules

theorem finiteSuppliedProgramRepresentation (S : Core.Signature) (rules : List (Core.Rule S)) :
    ∃ (D : Declarations) (p : AcceptedProgram D) (symbols : D.signature ⟶ S),
      p.resolved.map (Core.Rule.map symbols) = rules := by
  obtain ⟨D, localRules, symbols, same⟩ := finiteNamedProgramRepresentation S rules
  obtain ⟨p, compiled⟩ := localProgramByteRepresentation D localRules
  exact ⟨D, p, symbols, by rw [compiled]; exact same⟩

end Silmaril.Logic.Egg.Source.Named.FiniteSupport
