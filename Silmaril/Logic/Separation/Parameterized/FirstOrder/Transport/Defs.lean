module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {A B C : Signature}

def signatureMap (f : A ⟶ B) : signature A ⟶ signature B where
  sorts := id
  ops o := match o with
    | .value o => .value (f.operation o)
    | .unit => .unit
  rels r := match r with
    | .atom a => .atom (f.atom a)
    | .join => .join

private theorem folHom_ext {S T : FOL.Signature} (f g : S ⟶ T)
    (hs : f.sorts = g.sorts) (ho : HEq (@f.ops) (@g.ops)) (hr : HEq (@f.rels) (@g.rels)) : f = g := by
  cases f with
  | mk fb fr =>
    cases g with
    | mk gb gr =>
      cases fb with
      | mk fs fo =>
        cases gb with
        | mk gs go =>
          cases hs
          cases eq_of_heq ho
          cases eq_of_heq hr
          rfl

theorem signatureMap_id : signatureMap (𝟙 A) = 𝟙 (signature A) := by
  apply folHom_ext (signatureMap (𝟙 A)) (𝟙 (signature A)) rfl
  · apply heq_of_eq
    funext n w s o
    cases o <;> rfl
  · apply heq_of_eq
    funext n w r
    cases r <;> rfl

theorem signatureMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g := by
  apply folHom_ext (signatureMap (f ≫ g)) (signatureMap f ≫ signatureMap g) rfl
  · apply heq_of_eq
    funext n w s o
    cases o <;> rfl
  · apply heq_of_eq
    funext n w r
    cases r <;> rfl

def signatureFunctor : Signature ⥤ FOL.Signature where
  obj := signature
  map := signatureMap
  map_id _ := signatureMap_id
  map_comp := signatureMap_comp

private theorem folStructure_ext {S : FOL.Signature} (M N : FOL.Structure S)
    (hc : M.carrier = N.carrier) (ho : HEq (@M.op) (@N.op)) (hr : HEq (@M.rel) (@N.rel)) : M = N := by
  cases M with
  | mk mb mr =>
    cases N with
    | mk nb nr =>
      cases mb with
      | mk mc mo =>
        cases nb with
        | mk nc no =>
          cases hc
          cases eq_of_heq ho
          cases eq_of_heq hr
          rfl

/-- Canonical encoding commutes with the actual native FO reduct on objects. -/
theorem model_reduct (f : A ⟶ B) (M : Model B) :
    (Silmaril.Logic.FirstOrderLFP.reduct (signatureMap f)).obj (model M) = model (reduct f M) := by
  apply congrArg Silmaril.Logic.FirstOrderLFP.Model.mk
  apply folStructure_ext ((FOL.Structure.reduct (signatureMap f)).obj (model M).toStructure)
    (model (reduct f M)).toStructure rfl
  · apply heq_of_eq
    funext n w s o args
    cases o <;> rfl
  · apply heq_of_eq
    funext n w r args
    cases r <;> rfl

end Silmaril.Logic.Separation.Parameterized.FirstOrder
