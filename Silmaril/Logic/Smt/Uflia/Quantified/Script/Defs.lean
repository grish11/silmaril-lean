module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Institution.Thms
public import Silmaril.Logic.Smt.Uflia.Script.Thms

/-! Quantified single-query scripts with declarations in the sentence. The
source interpretation uses the independent expression interpreter, while the
abstract presentation uses typed quantified terms in one coherent global model. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified.Script
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution
open Silmaril.Logic.Smt.Uflia.SExpr
abbrev GroundScript := Silmaril.Logic.Smt.Uflia.Script.Layout

abbrev Problem (A : Signature String) := List (Quantified.Sentence A)

noncomputable def FixedHolds {A : Signature String} (problem : Problem A)
    (M : Model A) : Prop := ∀ sentence ∈ problem, sentence.Holds M

/-- Abstract whole problems share the interpretation of every typed global name. -/
structure Whole where
  environment : Environment
  assertions : Problem environment.signature

noncomputable def Whole.Holds (p : Whole) (M : Packaged.GlobalModel) : Prop :=
  FixedHolds p.assertions (M.reduct (Packaged.nameMap p.environment))

noncomputable def fixedPlain : Plain (Signature String) where
  Sen A := Problem A
  map f problem := problem.map (Quantified.Term.map f)
  map_id _ problem := by
    induction problem with
    | nil => rfl
    | cons sentence rest ih =>
        simp only [List.map_cons, Quantified.Term.map_id, ih]
  map_comp f g problem := by
    induction problem with
    | nil => rfl
    | cons sentence rest ih =>
        simp only [List.map_cons, Quantified.Term.map_comp, ih]
  Mod A := Model A
  reduct f M := M.reduct f
  reduct_id _ M := Model.reduct_id M
  reduct_comp f g M := Model.reduct_comp f g M
  Sat M problem := FixedHolds problem M
  sat_map f M problem := by
    simp only [FixedHolds, List.forall_mem_map, Quantified.Sentence.holds_map]

noncomputable abbrev fixedInstitution := fixedPlain.toInst
noncomputable abbrev fixedRoom (A : Signature String) := fixedPlain.room A

noncomputable def wholePlain : Plain (Disc Unit) where
  Sen _ := Whole
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Packaged.GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M p := p.Holds M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev wholeInstitution := wholePlain.toInst
noncomputable abbrev wholeRoom := wholePlain.room ()

/-- The quantified dialect admits UFLIA, or LIA with built-in nullary
declarations only. No quantifier-free tag is silently widened. -/
def layout? : List Expr → Option GroundScript
  | .list [.atom "set-logic", .atom "UFLIA"] :: rest =>
      Uflia.Script.commandBody? rest
  | .list [.atom "set-logic", .atom "LIA"] :: rest => do
      let body ← Uflia.Script.commandBody? rest
      if body.declarations.all Uflia.Script.liaDeclaration then some body else none
  | forms => Uflia.Script.commandBody? forms

/-- Successful decoding retains every expression, in order and with duplicates. -/
def assertions? (E : Environment) : (expressions : List Expr) →
    Option { assertions : List (Quantified.SExpr.Accepted E) //
      assertions.map (·.expression) = expressions }
  | [] => some ⟨[], rfl⟩
  | expression :: rest =>
      match decoded : Quantified.SExpr.decodeSentence? E expression with
      | none => none
      | some sentence => do
          let tail ← assertions? E rest
          pure ⟨⟨expression, sentence, decoded⟩ :: tail.val,
            by simp only [List.map_cons, tail.property]⟩

/-- Original text, reader result, command layout, decoded declaration prefix,
and all original assertions. These equations prohibit hidden assertion removal. -/
structure Accepted where
  text : String
  forms : List Expr
  layout : GroundScript
  checked : DeclarationPrefix
  assertions : List (Quantified.SExpr.Accepted checked.environment)
  reads : readForms text.toUTF8.data.toList = some forms
  shaped : layout? forms = some layout
  declarations_eq : checked.forms = layout.declarations
  assertions_eq : assertions.map (·.expression) = layout.assertions

def accept? (text : String) : Option Accepted :=
  match reads : readForms text.toUTF8.data.toList with
  | none => none
  | some forms =>
      match shaped : layout? forms with
      | none => none
      | some layout =>
          match decoded : declarations? layout.declarations with
          | none => none
          | some environment => do
              let checked : DeclarationPrefix := ⟨layout.declarations, environment, decoded⟩
              let assertions ← assertions? environment layout.assertions
              pure ⟨text, forms, layout, checked, assertions.val, reads, shaped,
                rfl, assertions.property⟩

def Accepted.toWhole (s : Accepted) : Whole :=
  ⟨s.checked.environment, s.assertions.map (·.sentence)⟩

/-- Direct source truth does not evaluate the decoded typed sentences. -/
noncomputable def Accepted.Holds (s : Accepted) (M : Packaged.GlobalModel) : Prop :=
  ∀ expression ∈ s.layout.assertions,
    Quantified.SExpr.Surface.Holds s.checked.environment
      (M.reduct (Packaged.nameMap s.checked.environment)) expression

noncomputable def Accepted.Sat (s : Accepted) : Prop := ∃ M, s.Holds M
noncomputable def Accepted.Unsat (s : Accepted) : Prop := ¬ s.Sat

noncomputable def plain : Plain (Disc Unit) where
  Sen _ := Accepted
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Packaged.GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M s := s.Holds M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev institution := plain.toInst
noncomputable abbrev room := plain.room ()

/-- Admission remains a separate obligation for both answers. -/
noncomputable def TextSat (text : String) : Prop := ∃ s, accept? text = some s ∧ s.Sat
noncomputable def TextUnsat (text : String) : Prop := ∃ s, accept? text = some s ∧ s.Unsat

end Silmaril.Logic.Smt.Uflia.Quantified.Script
