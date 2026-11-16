module

public import Silmaril.Logic.Egg.Source.Named.Representation.Local.Thms
public import Silmaril.Logic.Egg.Source.Named.Accepted.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named (LegalName finiteName finiteName_legal finiteName_injective
  canonicalContext canonicalContext_legal canonicalContext_profile)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance (s : String) : Decidable (Silmaril.Logic.Smt.SExpr.Writer.LegalAtom s) := by
  unfold Silmaril.Logic.Smt.SExpr.Writer.LegalAtom Silmaril.Logic.Smt.SExpr.Writer.LegalChar
  infer_instance

theorem eraseTerm_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ b ∈ Γ.bindings, LegalName b.name) {s : D.checked.LocalSort}
    (term : EQ.Term D.signature Γ.profile s) :
    Silmaril.Logic.Smt.SExpr.Writer.LegalExpr (Parser.encodeTerm (eraseTerm Γ term)) := by
  refine EQ.Term.rec (motive := fun _ term =>
    Silmaril.Logic.Smt.SExpr.Writer.LegalExpr (Parser.encodeTerm (eraseTerm Γ term))) ?_ ?_ term
  · intro i
    apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
    intro expression member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .atom (by decide)
    · exact .atom (legal _ (List.get_mem _ _)).1
  · intro n w s symbol arguments ih
    apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
    intro expression member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | rfl | member
    · exact .atom (by decide)
    · exact .atom ((D.checked.valid.2.2.2.1 symbol.val
        (List.mem_append_left _ symbol.property.1)).1.1)
    · exact .atom (D.checked.valid.2.2.1 _ s.property).1
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      exact ih i

theorem eraseEquality_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ b ∈ Γ.bindings, LegalName b.name)
    (e : Core.Equality D.signature Γ.profile) :
    Silmaril.Logic.Smt.SExpr.Writer.LegalExpr (Parser.encodeEquality (eraseEquality Γ e)) := by
  apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  simp only [eraseEquality, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .atom (by decide)
  · exact eraseTerm_legal Γ legal e.lhs
  · exact eraseTerm_legal Γ legal e.rhs

theorem eraseRule_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ b ∈ Γ.bindings, LegalName b.name) (label : String) (labelLegal : LegalName label)
    (guards : List (Core.Equality D.signature Γ.profile))
    (conclusion : Core.Equality D.signature Γ.profile) :
    Silmaril.Logic.Smt.SExpr.Writer.LegalExpr (Parser.encodeRule
      ⟨label, Γ.bindings, guards.map (eraseEquality Γ), eraseEquality Γ conclusion⟩) := by
  apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .atom (by decide)
  · exact .atom labelLegal.1
  · apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
    intro expression member
    obtain ⟨binding, bindingMember, equalExpression⟩ := List.mem_map.mp member
    rw [← equalExpression]
    apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
    intro expression member'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact .atom (legal binding bindingMember).1
    · obtain ⟨index, equal⟩ := List.mem_iff_get.mp bindingMember
      exact .atom (D.checked.valid.2.2.1 _ (by rw [← equal]; exact Γ.declared index)).1
  · apply Silmaril.Logic.Smt.SExpr.Writer.LegalExpr.list
    intro expression member
    obtain ⟨raw, rawMember, expressionEq⟩ := List.mem_map.mp member
    rw [← expressionEq]
    obtain ⟨e, _, rawEq⟩ := List.mem_map.mp rawMember
    rw [← rawEq]
    exact eraseEquality_legal Γ legal e
  · exact eraseEquality_legal Γ legal conclusion

/-- Every local rule has a fully parsed lexical representative with the chosen
fresh label. The statement includes the actual resolver equation. -/
theorem localRuleRepresentation_at {D : Declarations}
    (tuple : Σ n, Fin n → D.checked.LocalSort) (Γ : CheckedContext D)
    (legal : ∀ b ∈ Γ.bindings, LegalName b.name)
    (same : (⟨Γ.bindings.length, Γ.profile⟩ : Σ n, Fin n → D.checked.LocalSort) = tuple)
    (label : String) (labelLegal : LegalName label)
    (guards : List (Core.Equality D.signature tuple.2))
    (conclusion : Core.Equality D.signature tuple.2) :
    ∃ raw : RawRule, raw.name = label ∧
      resolveRule? D raw = some ⟨tuple.1, tuple.2, guards, conclusion⟩ ∧
      Silmaril.Logic.Smt.SExpr.Writer.LegalExpr (Parser.encodeRule raw) := by
  subst tuple
  exact ⟨⟨label, Γ.bindings, guards.map (eraseEquality Γ), eraseEquality Γ conclusion⟩,
    rfl, eraseRule_resolve Γ legal label guards conclusion,
    eraseRule_legal Γ legal label labelLegal guards conclusion⟩

theorem localRuleRepresentation (D : Declarations) (r : Core.Rule D.signature)
    (label : String) (labelLegal : LegalName label) :
    ∃ raw : RawRule, raw.name = label ∧ resolveRule? D raw = some r ∧
      Silmaril.Logic.Smt.SExpr.Writer.LegalExpr (Parser.encodeRule raw) :=
  localRuleRepresentation_at ⟨r.scope, r.context⟩ (canonicalContext r.context)
    (canonicalContext_legal r.context) (canonicalContext_profile r.context)
    label labelLegal r.guards r.conclusion

/-- Ordered finite tuple traversal retains exact positions. -/
theorem mapM_ofFn {α β : Type} (f : α → Option β) (n : Nat)
    (xs : Fin n → α) (ys : Fin n → β) (success : ∀ i, f (xs i) = some (ys i)) :
    (List.ofFn xs).mapM f = some (List.ofFn ys) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.ofFn_succ, success 0,
        ih (fun i => xs i.succ) (fun i => ys i.succ) (fun i => success i.succ)]

/-- Every finite ordered local rule file has actual accepted complete bytes.
Neither a selected entry nor set equality substitutes for list equality. -/
theorem localProgramByteRepresentation (D : Declarations) (rules : List (Core.Rule D.signature)) :
    ∃ p : AcceptedProgram D, p.resolved = rules := by
  classical
  choose raw properties using (fun i : Fin rules.length =>
    localRuleRepresentation D (rules.get i) (finiteName i.val) (finiteName_legal i.val))
  let program : RawProgram := List.ofFn raw
  have names : program.map RawRule.name = List.ofFn (fun i : Fin rules.length => finiteName i.val) := by
    simp only [program, List.map_ofFn]
    congr 1
    funext i
    exact (properties i).1
  have valid : (program.map RawRule.name).Nodup ∧ ∀ r ∈ program, LegalName r.name := by
    constructor
    · rw [names]
      apply List.nodup_ofFn.mpr
      intro i j equal
      exact Fin.ext (finiteName_injective equal)
    · intro r member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      rw [(properties i).1]
      exact finiteName_legal i.val
  have resolved : resolveProgram? D program = some rules := by
    unfold resolveProgram?
    rw [ite_eq_left valid]
    have complete := mapM_ofFn (resolveRule? D) rules.length raw rules.get
      (fun i => (properties i).2.1)
    simpa only [List.ofFn_get] using complete
  have legal : ∀ expression ∈ program.map Parser.encodeRule,
      Silmaril.Logic.Smt.SExpr.Writer.LegalExpr expression := by
    intro expression member
    obtain ⟨r, ruleMember, expressionEq⟩ := List.mem_map.mp member
    rw [← expressionEq]
    obtain ⟨i, ruleEq⟩ := List.mem_ofFn.mp ruleMember
    rw [← ruleEq]
    exact (properties i).2.2
  exact ⟨⟨Parser.writeProgram program, program, Parser.read_write_program program legal,
    rules, resolved⟩, rfl⟩

end Silmaril.Logic.Egg.Source.Named
