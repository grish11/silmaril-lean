module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Thms
public import Silmaril.Logic.Institution.Faithful

/-! Signature change for literal-subset models. Signature maps may identify
sorts and operation symbols; no extra injectivity or filtration premise occurs. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Representation
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Reduct keeps the same ambient values and restricts the carrier/operation
families along the actual monotone signature map. -/
def LiteralModel.reduct {A B : Signature} (f : A ⟶ B) (L : LiteralModel B) : LiteralModel A where
  ambient := L.ambient
  carrier s := L.carrier (f.base.sorts s)
  inclusion := fun h => L.inclusion (f.monotone h)
  op o := L.op (f.base.ops o)

def literalReductFunctor {A B : Signature} (f : A ⟶ B) : LiteralModel B ⥤ LiteralModel A where
  obj := LiteralModel.reduct f
  map h := {
    map := fun s => h.map (f.base.sorts s)
    map_op := by
      intro n w s o args
      cases o with
      | base b => exact h.map_op (.base (f.base.ops b)) args
      | inclusion s t hst =>
        exact h.map_op (.inclusion _ _ (f.monotone hst)) args }
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.Algebraic.OrderSorted.Representation
