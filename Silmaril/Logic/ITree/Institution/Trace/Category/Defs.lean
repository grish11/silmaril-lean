module

public import Silmaril.Logic.ITree.Institution.Trace.Thms
public import Silmaril.Semantics.ITree.Signature.Trace.Category.Defs

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

/-- The existing trace sentences, with an all-lifts map on each arrow. -/
def liftSentences : Signature.InjectiveRequests.{u} ⥤ Type (max (u + 1) (v + 1)) where
  obj S := Sentence.{u,v} ⟨S.obj⟩
  map {S T} f := TypeCat.ofHom (Sentence.translateLift (S := ⟨S.obj⟩) (T := ⟨T.obj⟩) f.hom)
  map_id _ := congrArg TypeCat.ofHom (funext Sentence.translateLift_id)
  map_comp {S T U} f g := congrArg TypeCat.ofHom (funext fun φ =>
    Sentence.translateLift_comp (S := ⟨S.obj⟩) (T := ⟨T.obj⟩) (U := ⟨U.obj⟩) f.hom g.hom φ)

/-- The handled-trace institution on injective complete request maps, with
the original discrete handler models and their existing reduct. -/
def liftInstitution : Silmaril.Logic.Institution.ClassicInstitution.{u + 1, u + 1,
    max (u + 1) (v + 1), max (u + 1) (w + 1), max (u + 1) (w + 1)} Signature.InjectiveRequests.{u} where
  Sen := liftSentences.{u,v}
  Mod := (wideSubcategoryInclusion Signature.injectiveRequests).op ⋙ Silmaril.Logic.ITree.models.{u,w}
  Sat S M φ := Sat (S := ⟨S.obj⟩) M.as φ
  satisfaction {S T} f M φ :=
    satisfaction_lift (S := ⟨S.obj⟩) (T := ⟨T.obj⟩) f.hom f.property M.as φ

end Silmaril.Logic.ITree.TraceInstitution
