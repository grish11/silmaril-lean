module

public import Silmaril.Logic.TypeTheory.LambdaPi.Signature.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Signature

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Logic.Institution

/-- Checked signatures have no duplicate names. -/
theorem Signature.Checked.names_nodup {S : Signature} (h : S.Checked) :
    (S.map Declaration.name).Nodup :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.signature_nodup h

/-- A checked name has exactly one declared type. -/
theorem Signature.Checked.unique_type {S : Signature} (h : S.Checked)
    {c : String} {A B : Term} (hA : Declaration.mk c A ∈ S) (hB : Declaration.mk c B ∈ S) : A = B :=
  congrArg Declaration.type (List.inj_on_of_nodup_map h.names_nodup hA hB rfl)

/-- Later declarations preserve every derivation over the earlier signature. -/
theorem Signature.derives_inclusion {S T : Signature} (h : S ⊆ T)
    {H : Set Judgment} {J : Judgment} (hd : Derives S.calculus H J) :
    Derives T.calculus H J :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.signature_derives_inclusion h hd

/-- Every declared type is sorted in the final checked signature. -/
theorem Signature.Checked.declared_sorted {S : Signature} (h : S.Checked)
    {c : String} {A : Term} (hd : Declaration.mk c A ∈ S) :
    ∃ s, Derives S.calculus ∅ ⟨[], A, Term.univ s⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.signature_declared_sorted h hd

/-- Consequently every declaration supplies an actual typing derivation of its constant. -/
theorem Signature.Checked.constant_typed {S : Signature} (h : S.Checked)
    {c : String} {A : Term} (hd : Declaration.mk c A ∈ S) :
    Derives S.calculus ∅ ⟨[], Term.constant c, A⟩ := by
  obtain ⟨s, hs⟩ := h.declared_sorted hd
  exact .constant hd hs

/-- Structural translations between the underlying calculi form a category of checked signatures. -/
instance : Category CheckedSignature where
  Hom S T := S.calculus ⟶ T.calculus
  id S := 𝟙 S.calculus
  comp F G := F ≫ G
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

/-- Forget only the signature-checking certificate. -/
def checkedSignaturesToCalculi : CheckedSignature ⥤ Calculus where
  obj := CheckedSignature.calculus
  map F := F
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Checked LF signatures inherit the already proved institution and Hets interpretation. -/
noncomputable def checkedSignatureInstitutions : CheckedSignature ⥤ CoIns.{0,0,0,0,0} :=
  checkedSignaturesToCalculi ⋙ calculusToInstitutions

/-- The category of checked signatures supplies a Hets graph through the same functor. -/
noncomputable def checkedSignatureHets :=
  IndexedCoInst.toLogicGraph checkedSignatureInstitutions

end Silmaril.Logic.TypeTheory.LambdaPi
