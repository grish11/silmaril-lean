module

public import Silmaril.Logic.Egglog.Core.FirstOrder

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Graph

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The graph signature follows constructor, predicate, table and sort maps. -/
def signatureMap {S T : Signature} (f : S ⟶ T) : signature S ⟶ signature T where
  sorts := f.sorts
  ops := f.ops
  rels := fun r => match r with
    | .predicate p => .predicate (f.rels p)
    | .row t => .row (f.functions t)

def signatures : Signature ⥤ FOL.Signature where
  obj := signature
  map := signatureMap
  map_id S := by
    change FOL.Signature.Hom.mk _ _ = FOL.Signature.Hom.mk _ _
    congr 1
    funext n w r
    cases r <;> rfl
  map_comp f g := by
    change FOL.Signature.Hom.mk _ _ = FOL.Signature.Hom.mk _ _
    congr 1
    funext n w r
    cases r <;> rfl

/-- The independent graph interpretation commutes with the original model reduct. -/
theorem model_reduct {S T : Signature} (f : S ⟶ T) (M : Model T) :
    model ((Model.reduct f).obj M) = (FOL.Structure.reduct (signatureMap f)).obj (model M) := by
  change FOL.Structure.mk _ _ = FOL.Structure.mk _ _
  congr 1
  funext n w r
  cases r <;> rfl

def reindex {S T : Signature} (f : S ⟶ T) : room S ⟶ room T where
  sen := FOL.Sentence.map (signatureMap f)
  mod := Model.reduct f
  sat (M : Model T) s := by
    change (s.map (signatureMap f)).Holds (model M) ↔
      s.Holds (model ((Model.reduct f).obj M))
    rw [model_reduct]
    exact FOL.Sentence.holds_map (signatureMap f) (model M) s

/-- Full first-order formulas over graph signatures, interpreted in functional
partial-table models. Empty tables and empty carriers remain permitted. -/
def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := reindex
  map_id S := by
    apply Room.hom_ext (f := reindex (𝟙 S)) (g := 𝟙 (room S))
    · funext s
      change s.map (signatures.map (𝟙 S)) = s
      rw [signatures.map_id]
      exact FOL.Sentence.map_id s
    · rfl
  map_comp f g := by
    apply Room.hom_ext (f := reindex (f ≫ g)) (g := reindex f ≫ reindex g)
    · funext s
      change s.map (signatures.map (f ≫ g)) =
        (s.map (signatures.map f)).map (signatures.map g)
      rw [signatures.map_comp]
      exact FOL.Sentence.map_comp _ _ s
    · rfl

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

end Silmaril.Logic.Egglog.Core.Graph
