module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Source.Thms
import all Init.Data.String.Search
import all Init.Data.String.Slice.Numeric
import all Init.Data.String.Slice.Pattern
import all Init.Data.String.Basic
import all Init.Data.Int.Repr
import all Init.Data.Repr

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples

/-- Equality cannot manufacture truth from two unsupported operands. -/
theorem unsupported_equality (ρ : Environment) :
    denote ρ (.equals "SortBool" "SortGeneratedTopCell"
      (.unsupported "unknown") (.unsupported "unknown")) .config = none := rfl

theorem wrong_sort_variable (ρ : Environment) (name : String) :
    denote ρ (.variable name "SortBool") .integer = none := rfl

/-- Defined empty intersections are different from unsupported syntax. -/
theorem defined_empty (ρ : Environment) :
    denote ρ (.and "SortBool" (.domainValue "SortBool" "true")
      (.domainValue "SortBool" "false")) .boolean = some ∅ := by
  simp [denote, sortName]

/-- Original as-pattern captures remain independent and can disagree. -/
theorem capture_mismatch (Γ : Context) (ρ : Environment) (r : Rule)
    (mismatch : ρ .integer Γ.x ≠ ρ .valcell Γ.capturedVal) :
    denote ρ (leftTree Γ r) .config = some ∅ := by
  rw [leftTree_denote]
  simp [decode, mismatch]

/-- A source claim is checked information, never an operational axiom. -/
theorem claims_no_step (ds : List Declaration)
    (claims : ∀ decl ∈ ds, decl.kind = .claim) (c d : Config) : ¬ RawStep ds c d := by
  rintro ⟨decl, member, isAxiom, _⟩
  have impossible := (claims decl member).symm.trans isAxiom
  cases impossible

set_option maxRecDepth 16000 in
/-- Existing unchanged authored bytes now have an independent Raw-AST step. -/
theorem actual_zero_bytes (tail : List String) :
    ∃ p, check authoredZeroBytes = some p ∧
      RawStep p.declarations ⟨"a" :: tail, 0, 7⟩ ⟨"b" :: tail, 0, 11⟩ := by
  have accepted := authored_zero_checked
  cases hp : check authoredZeroBytes with
  | none => simp [hp] at accepted
  | some p =>
    have rules : p.axioms = [⟨"a", "b", .zero, .counter, 11⟩] := by
      simpa only [hp, Option.map_some, Option.some.injEq] using accepted
    refine ⟨p, rfl, (rawStep_iff_step (p := p) hp _ _).2 ?_⟩
    rw [rules]
    exact authored_zero_old7_new11 tail

set_option maxRecDepth 16000 in
theorem actual_nonzero_bytes (tail : List String) (x : Int) (nonzero : x ≠ 0) :
    ∃ p, check authoredNonzeroBytes = some p ∧
      RawStep p.declarations ⟨"a" :: tail, x, 7⟩ ⟨"c" :: tail, x, 13⟩ := by
  have accepted := authored_nonzero_checked
  cases hp : check authoredNonzeroBytes with
  | none => simp [hp] at accepted
  | some p =>
    have rules : p.axioms = [⟨"a", "c", .nonzero, .counter, 13⟩] := by
      simpa only [hp, Option.map_some, Option.some.injEq] using accepted
    refine ⟨p, rfl, (rawStep_iff_step (p := p) hp _ _).2 ?_⟩
    rw [rules]
    exact authored_nonzero_old7_new13 tail x nonzero

def names : Context := ⟨"Tail", "X", "CapturedVal", "Counter"⟩
def valRule : Rule := ⟨"a", "b", .zero, .val, 5⟩
def counterRule : Rule := ⟨"a", "c", .zero, .counter, 11⟩
def valDeclaration : Declaration := ⟨.ruleAxiom, [], valRule.tree names, []⟩
def counterDeclaration : Declaration := ⟨.ruleAxiom, [], counterRule.tree names, []⟩

theorem val_declaration_checked : elaborate valDeclaration = some (names, valRule) := by cbv

theorem counter_declaration_checked :
    elaborate counterDeclaration = some (names, counterRule) := by cbv

/-- Both targets are supported. Overlapping source axioms retain both successors;
the source relation introduces neither a priority nor a first-match policy. -/
theorem nondeterministic_targets (tail : List String) :
    RawStep [valDeclaration, counterDeclaration]
      ⟨"a" :: tail, 0, 7⟩ ⟨"b" :: tail, 5, 7⟩ ∧
    RawStep [valDeclaration, counterDeclaration]
      ⟨"a" :: tail, 0, 7⟩ ⟨"c" :: tail, 0, 11⟩ ∧
    (⟨"b" :: tail, 5, 7⟩ : Config) ≠ ⟨"c" :: tail, 0, 11⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · exact rawStep_of_elaborate (by simp) rfl val_declaration_checked
      ⟨tail, 0, 0, 7⟩ rfl (by simp [valRule, Guard.Holds, Guard.eval, intEqual])
  · exact rawStep_of_elaborate (by simp) rfl counter_declaration_checked
      ⟨tail, 0, 0, 7⟩ rfl (by simp [counterRule, Guard.Holds, Guard.eval, intEqual])
  · intro equal
    have impossible := congrArg Config.val equal
    norm_num at impossible

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source.Examples
