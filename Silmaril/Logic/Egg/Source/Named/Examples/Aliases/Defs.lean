module

public import Silmaril.Logic.Egg.Source.Named.Examples.Defs
public import Silmaril.Logic.Egg.Source.Named.Supplied.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- One ambient operation at every profile permits actual aliases of names. -/
def aliasSignature : Core.Signature := ⟨Unit, fun _ _ _ => Unit⟩

def aliasSymbols (D : Declarations) : D.signature ⟶ aliasSignature where
  sorts := fun _ => ()
  ops := fun _ => ()

/-- The shared carrier is populated and its operations need not be free. -/
def aliasModel : Core.Model aliasSignature where
  carrier := fun _ => Bool
  op := fun _ _ => false

def aliasLeftSource : String :=
  "(rewrite left () () (equal (app z A) (app z A)))"

def aliasRightSource : String :=
  "(rewrite right () () (equal (app w B) (app w B)))"

def aliasLeftProgram : AcceptedInferredProgram :=
  (acceptInferred? (sourceBytes aliasLeftSource)).get (by decide +kernel)

def aliasRightProgram : AcceptedInferredProgram :=
  (acceptInferred? (sourceBytes aliasRightSource)).get (by decide +kernel)

def aliasLeft : FamilySentence aliasSignature :=
  ⟨.inferred aliasLeftProgram, aliasSymbols _⟩

def aliasRight : FamilySentence aliasSignature :=
  ⟨.inferred aliasRightProgram, aliasSymbols _⟩

/-- The executable receipts genuinely retain distinct local sort and
constructor spellings before their shared ambient interpretation. -/
theorem alias_local_names :
    aliasLeftProgram.declarations.checked.data.sorts = ["A"] ∧
    aliasRightProgram.declarations.checked.data.sorts = ["B"] ∧
    aliasLeftProgram.declarations.checked.data.constructors.map
      Silmaril.Logic.Egglog.Source.Named.TotalDeclaration.name = ["z"] ∧
    aliasRightProgram.declarations.checked.data.constructors.map
      Silmaril.Logic.Egglog.Source.Named.TotalDeclaration.name = ["w"] := by
  decide +kernel

/-- A nullary ambient term has no argument coordinates to distinguish. -/
def aliasNullary {n : Nat} (Γ : Fin n → aliasSignature.S) (s : aliasSignature.S) :
    EQ.Term aliasSignature Γ s :=
  .app (n := 0) (w := fun _ => ()) () (fun i => Fin.elim0 i)

/-- This kernel-reducible projection records only the relevant term shape. It does
not decide equality of dependent terms or invoke an external evaluator. -/
noncomputable def aliasTermShape {n : Nat} {Γ : Fin n → aliasSignature.S} {s : aliasSignature.S}
    (term : EQ.Term aliasSignature Γ s) : Bool :=
  EQ.Term.rec (motive := fun _ _ => Bool) (fun _ => false)
    (fun {arity : Nat} {_inputs} {_output} _operation _arguments _hypotheses => arity == 0) term

theorem aliasTermShape_sound {n : Nat} {Γ : Fin n → aliasSignature.S}
    {s : aliasSignature.S} (term : EQ.Term aliasSignature Γ s)
    (shape : aliasTermShape term = true) : term = aliasNullary Γ s := by
  refine EQ.Term.rec (motive := fun s term => aliasTermShape term = true →
    term = aliasNullary Γ s) ?_ ?_ term shape
  · intro i impossible
    change false = true at impossible
    cases impossible
  · intro arity inputs output operation arguments _ success
    have zero : arity = 0 := by
      change (arity == 0) = true at success
      exact beq_iff_eq.mp success
    subst arity
    have inputsEq : inputs = fun _ : Fin 0 => () := Subsingleton.elim _ _
    subst inputs
    have operationEq : operation = () := by
      change (_ : Unit) = ()
      exact Subsingleton.elim _ _
    subst operation
    have argumentsEq : arguments = fun i : Fin 0 => Fin.elim0 i := by
      funext i
      exact Fin.elim0 i
    rw [argumentsEq]
    rfl

/-- The unique closed, unguarded ambient rule with two nullary applications. -/
def aliasAmbientRule : Core.Rule aliasSignature :=
  ⟨0, fun _ => (), [], ⟨(), aliasNullary (fun _ => ()) (), aliasNullary (fun _ => ()) ()⟩⟩

noncomputable def aliasRuleShape : Core.Rule aliasSignature → Bool
  | ⟨0, _, [], conclusion⟩ => aliasTermShape conclusion.lhs && aliasTermShape conclusion.rhs
  | _ => false

theorem aliasRuleShape_sound (r : Core.Rule aliasSignature)
    (shape : aliasRuleShape r = true) : r = aliasAmbientRule := by
  rcases r with ⟨scope, context, guards, ⟨sort, left, right⟩⟩
  cases scope with
  | succ scope => simp [aliasRuleShape] at shape
  | zero =>
      cases guards with
      | cons guard guards => simp [aliasRuleShape] at shape
      | nil =>
          have shapes : aliasTermShape left = true ∧ aliasTermShape right = true :=
            by simpa only [aliasRuleShape, Bool.and_eq_true] using shape
          have contextEq : context = fun _ : Fin 0 => () := Subsingleton.elim _ _
          subst context
          cases sort
          rw [aliasTermShape_sound left shapes.1, aliasTermShape_sound right shapes.2]
          rfl

theorem aliasListShape_sound (rules : List (Core.Rule aliasSignature))
    (shape : rules.map aliasRuleShape = [true]) : rules = [aliasAmbientRule] := by
  cases rules with
  | nil => simp at shape
  | cons first rest =>
      have fields := List.cons.inj shape
      have empty : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [List.length_map, List.length_nil] using congrArg List.length fields.2
      subst rest
      rw [aliasRuleShape_sound first fields.1]

/-- Kernel-checked finite shape computations refer to the actual accepted
inferred files; soundness above recovers equality of dependent ambient rules. -/
theorem aliasLeft_resolved :
    aliasLeft.receipt.program.resolved.map (Core.Rule.map aliasLeft.symbols) = [aliasAmbientRule] := by
  apply aliasListShape_sound
  decide +kernel

theorem aliasRight_resolved :
    aliasRight.receipt.program.resolved.map (Core.Rule.map aliasRight.symbols) = [aliasAmbientRule] := by
  apply aliasListShape_sound
  decide +kernel

/-- Distinct whole source files and local sorts map to the same ambient rule.
The original receipts survive; local name equality is not ambient identity. -/
theorem distinct_bytes_same_ambient :
    aliasLeft.receipt.program.bytes ≠ aliasRight.receipt.program.bytes ∧
      aliasLeft.decode = aliasRight.decode := by
  refine ⟨by decide +kernel, ?_⟩
  have same := aliasLeft_resolved.trans aliasRight_resolved.symm
  ext r
  change (∃ original ∈ aliasLeft.receipt.program.resolved,
    original.map aliasLeft.symbols = r) ↔
    ∃ original ∈ aliasRight.receipt.program.resolved,
      original.map aliasRight.symbols = r
  rw [← List.mem_map, same, List.mem_map]

theorem aliases_share_populated_model : aliasLeft.Holds aliasModel ∧ aliasRight.Holds aliasModel := by
  have left : ∀ r ∈ aliasLeft.decode, r.Holds aliasModel := by
    intro r member
    have mapped : r ∈ aliasLeft.receipt.program.resolved.map (Core.Rule.map aliasLeft.symbols) :=
      List.mem_map.mpr member
    rw [aliasLeft_resolved] at mapped
    have equal := List.mem_singleton.mp mapped
    subst r
    intro values _
    rfl
  exact ⟨(aliasLeft.decode_holds aliasModel).mp left,
    (aliasRight.decode_holds aliasModel).mp
      (distinct_bytes_same_ambient.2 ▸ left)⟩

/-- A source theory is checked in that one actual populated ambient model. -/
theorem aliases_one_theory_model :
    TheoryHolds aliasModel ({aliasLeft, aliasRight} : Set (FamilySentence aliasSignature)) := by
  intro p member
  rcases Set.mem_insert_iff.mp member with equal | member
  · subst p
    exact aliases_share_populated_model.1
  · have equal := Set.mem_singleton_iff.mp member
    subst p
    exact aliases_share_populated_model.2

/-- Direct supplied transport preserves the original complete file bytes. -/
theorem supplied_transport_keeps_bytes {S T : SuppliedSignature} (f : S ⟶ T)
    (p : Supplied.Direct.Sentence S) :
    (Supplied.Direct.map f p).bytes = p.bytes := rfl

/-- The final rule matters even when the first rule is vacuously true. -/
theorem dropping_last_rule_changes_truth :
    unusedRaw.Holds emptySortModel ∧
      ¬ RawProgram.Holds emptySortModel [unusedRaw, pairRaw] := by
  exact ⟨original_context_changes_truth.2,
    fun h => original_context_changes_truth.1 (h pairRaw (by simp))⟩

end Silmaril.Logic.Egg.Source.Named.Examples
