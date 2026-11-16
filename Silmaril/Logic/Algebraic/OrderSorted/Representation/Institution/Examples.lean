module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Thms

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Representation.InstitutionExamples
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- All profiles have two source operation symbols; the target identifies them. -/
abbrev source : Signature := discrete ⟨Bool, fun _ _ _ => Bool⟩
abbrev target : Signature := discrete ⟨Unit, fun _ _ _ => Unit⟩

def collapse : source ⟶ target where
  base := {
    sorts := fun _ => ()
    ops := fun _ => () }
  monotone := fun _ _ _ => rfl

/-- A target literal model with the single actual ambient value. -/
def singleton : LiteralModel target where
  ambient := Unit
  carrier := fun _ => Set.univ
  inclusion := fun _ _ _ => trivial
  op := fun _ _ => ⟨(), trivial⟩

/-- Neither sort injectivity nor operation-symbol injectivity is required. -/
theorem collapse_sorts : collapse.base.sorts true = collapse.base.sorts false := rfl

theorem collapse_ops :
    collapse.base.ops (n := 0) (w := Fin.elim0) (s := true) true =
      collapse.base.ops (n := 0) (w := Fin.elim0) (s := true) false := rfl

/-- Both source sorts are literal subsets of exactly the unchanged ambient type. -/
theorem reduct_ambient : (singleton.reduct collapse).ambient = singleton.ambient := rfl

def constantsEqual : Sentence source := {
  k := 0
  ctx := Fin.elim0
  sort := true
  lhs := .app (n := 0) (w := Fin.elim0) (.base true) (fun i => i.elim0)
  rhs := .app (n := 0) (w := Fin.elim0) (.base false) (fun i => i.elim0) }

/-- A sentence uses the actual existing translation and target evaluation. -/
theorem constantsEqual_target : (sentenceMap collapse constantsEqual).Holds singleton.algebra := by
  intro _
  rfl

theorem constantsEqual_reduct : constantsEqual.Holds (singleton.reduct collapse).algebra :=
  (literal_satisfaction collapse singleton constantsEqual).mp constantsEqual_target

/-- Compilation and reduct agree as models, not merely on a selected equation. -/
theorem compiled_reduct :
    (singleton.reduct collapse).model = reduct collapse singleton.model :=
  compile_reduct collapse singleton

end Silmaril.Logic.Algebraic.OrderSorted.Representation.InstitutionExamples
