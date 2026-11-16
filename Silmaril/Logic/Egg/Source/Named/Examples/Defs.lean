module

public import Silmaril.Logic.Egg.Source.Named.Theory.Defs
public import Silmaril.Logic.Egg.Source.Named.Representation.Local.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two types, no operations: the second type may have no values. -/
def twoSorts : Declarations :=
  ⟨⟨⟨["A", "E"], [], [], []⟩, by decide⟩, rfl, rfl⟩

def sortA : twoSorts.checked.LocalSort := ⟨"A", by decide⟩
def sortE : twoSorts.checked.LocalSort := ⟨"E", by decide⟩

def emptySortModel : Core.Model twoSorts.signature where
  carrier := fun s => if s.val = "E" then Empty else Bool
  op := fun o _ => False.elim (by simpa [twoSorts] using o.property.1)

def pairContext : CheckedContext twoSorts :=
  ⟨[⟨"x", "A"⟩, ⟨"y", "A"⟩], by decide, by decide⟩

def unusedContext : CheckedContext twoSorts :=
  ⟨[⟨"x", "A"⟩, ⟨"y", "A"⟩, ⟨"unused", "E"⟩], by decide, by decide⟩

def pairEquality : Core.Equality twoSorts.signature pairContext.profile :=
  ⟨sortA, .var ⟨0, by decide⟩,
    EQ.Term.var (Sg := twoSorts.signature) (Γ := pairContext.profile) ⟨1, by decide⟩⟩

def unusedEquality : Core.Equality twoSorts.signature unusedContext.profile :=
  ⟨sortA, .var ⟨0, by decide⟩,
    EQ.Term.var (Sg := twoSorts.signature) (Γ := unusedContext.profile) ⟨1, by decide⟩⟩

def pairRule : Core.Rule twoSorts.signature :=
  ⟨2, pairContext.profile, [], pairEquality⟩

def unusedRule : Core.Rule twoSorts.signature :=
  ⟨3, unusedContext.profile, [], unusedEquality⟩

def pairRaw : RawRule :=
  ⟨"collapse", pairContext.bindings, [], eraseEquality pairContext pairEquality⟩

def unusedRaw : RawRule :=
  ⟨"unused-empty", unusedContext.bindings, [], eraseEquality unusedContext unusedEquality⟩

theorem pair_resolved : resolveRule? twoSorts pairRaw = some pairRule :=
  eraseRule_resolve pairContext (by decide) "collapse" [] pairEquality

theorem unused_resolved : resolveRule? twoSorts unusedRaw = some unusedRule :=
  eraseRule_resolve unusedContext (by decide) "unused-empty" [] unusedEquality

/-- Requiring all pairs in a populated Boolean type to be equal is false. -/
theorem pair_rule_false : ¬ pairRule.Holds emptySortModel := by
  intro holds
  let values : Valuation emptySortModel pairContext := by
    change (i : Fin 2) → emptySortModel.carrier (pairContext.profile i)
    exact Fin.cases (motive := fun i : Fin 2 =>
      emptySortModel.carrier (pairContext.profile i)) false
      (Fin.cases (motive := fun i : Fin 1 =>
        emptySortModel.carrier (pairContext.profile i.succ)) true (fun i => Fin.elim0 i))
  have bad := holds values (fun _ member => False.elim (List.not_mem_nil member))
  change (false : Bool) = true at bad
  cases bad

/-- An unused binder of an empty type makes the full universal rule vacuous.
Dropping that binder would turn this true rule into the false rule above. -/
theorem unused_rule_true : unusedRule.Holds emptySortModel := by
  intro values _
  exact Empty.elim (values ⟨2, by decide⟩)

theorem original_context_changes_truth :
    ¬ pairRaw.Holds emptySortModel ∧ unusedRaw.Holds emptySortModel := by
  exact ⟨fun h => pair_rule_false
    ((resolveRule_holds_iff twoSorts pairRaw pairRule pair_resolved emptySortModel).mp h),
    (resolveRule_holds_iff twoSorts unusedRaw unusedRule unused_resolved emptySortModel).mpr
      unused_rule_true⟩

/-- Every sort can instead be populated without changing the signature. -/
def boolModel : Core.Model twoSorts.signature where
  carrier := fun _ => Bool
  op := fun o _ => False.elim (by simpa [twoSorts] using o.property.1)

def collapse : EQ.Algebra.Hom boolModel (singletonModel twoSorts.signature) where
  map := fun _ _ => ()
  map_op := fun _ _ => rfl

/-- This is an ordinary arrow in the source rooms, despite identifying values. -/
theorem collapse_not_injective : ¬ Function.Injective (collapse.map sortA) := by
  intro injective
  have bad : (false : Bool) = true := injective rfl
  cases bad

def sourceBytes (source : String) : List UInt8 := source.toUTF8.toList

/-- A complete two-rule file with a guard, a right-only variable, an unused
type, and a nested operation. Both modes keep the entire original file. -/
def completeSource : String :=
  "(rewrite first ((x A) (y A) (unused E)) " ++
  "((equal (var x) (var y))) " ++
  "(equal (app f A (app f A (var x))) (app f A (var y)))) " ++
  "(rewrite second ((right A)) () (equal (app z A) (var right)))"

theorem complete_source_admitted :
    (acceptInferred? (sourceBytes completeSource)).isSome = true := by decide +kernel

/-- Every original rule survives, in order, in the accepted receipt. -/
theorem complete_source_two_rules :
    ((acceptInferred? (sourceBytes completeSource)).map
      (fun p => p.program.resolved.length)) = some 2 := by decide +kernel

/-- Unsupported trailing syntax and inconsistent occurrence profiles reject. -/
example : (acceptInferred? (sourceBytes (completeSource ++ " (run 1)"))).isNone = true := by
  decide +kernel
example : (acceptInferred? (sourceBytes
  "(rewrite r ((x A)) () (equal (app f A (var x)) (app f B (var x))))")).isNone = true := by
  decide +kernel
example : (acceptInferred? (sourceBytes
  "(rewrite r ((x A)) () (equal (app f A (var x)) (app f A)))")).isNone = true := by
  decide +kernel

/-- Scope, complete contexts, result sorts, labels and parentheses are checked. -/
example : (acceptInferred? (sourceBytes
  "(rewrite r ((x A) (x A)) () (equal (var x) (var x)))")).isNone = true := by
  decide +kernel
example : (acceptInferred? (sourceBytes
  "(rewrite r ((x A)) () (equal (var x) (var absent)))")).isNone = true := by
  decide +kernel
example : (acceptInferred? (sourceBytes
  "(rewrite r ((x A) (y B)) () (equal (var x) (var y)))")).isNone = true := by
  decide +kernel
example : (acceptInferred? (sourceBytes
  ("(rewrite r ((x A)) () (equal (var x) (var x))) " ++
  "(rewrite r ((y A)) () (equal (var y) (var y)))"))).isNone = true := by
  decide +kernel
example : (acceptInferred? (sourceBytes
  "(rewrite r ((x A)) () (equal (var x) (var x))")).isNone = true := by
  decide +kernel

end Silmaril.Logic.Egg.Source.Named.Examples
