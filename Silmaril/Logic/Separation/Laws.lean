module

public import Silmaril.Logic.Separation.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation

theorem Resource.sep_comm (R : Resource) (P Q : Set R.carrier) : R.sep P Q = R.sep Q P := by
  ext h
  constructor <;> rintro ⟨a,b,hj,ha,hb⟩
  · exact ⟨b,a,(R.comm _ _ _).mp hj,hb,ha⟩
  · exact ⟨b,a,(R.comm _ _ _).mp hj,hb,ha⟩

theorem Resource.sep_assoc (R : Resource) (P Q T : Set R.carrier) :
    R.sep (R.sep P Q) T = R.sep P (R.sep Q T) := by
  ext h
  constructor
  · rintro ⟨ab,c,hj,⟨a,b,hab,ha,hb⟩,hc⟩
    obtain ⟨bc,hbc,hh⟩ := (R.assoc a b c h).mp ⟨ab,hab,hj⟩
    exact ⟨a,bc,hh,ha,b,c,hbc,hb,hc⟩
  · rintro ⟨a,bc,hj,ha,⟨b,c,hbc,hb,hc⟩⟩
    obtain ⟨ab,hab,hh⟩ := (R.assoc a b c h).mpr ⟨bc,hbc,hj⟩
    exact ⟨ab,c,hh,⟨a,b,hab,ha,hb⟩,hc⟩

theorem Resource.emp_sep (R : Resource) (P : Set R.carrier) : R.sep {R.unit} P = P := by
  ext h
  constructor
  · rintro ⟨a,b,hj,ha,hb⟩
    have ha' : a = R.unit := ha
    have hb' : b = h := (R.unit_join b h).mp (ha' ▸ hj)
    exact hb' ▸ hb
  · intro hp
    exact ⟨R.unit,h,(R.unit_join h h).mpr rfl,rfl,hp⟩

theorem Resource.residuation (R : Resource) (P Q T : Set R.carrier) :
    R.sep P Q ⊆ T ↔ P ⊆ R.wand Q T := by
  constructor
  · intro h a ha b c hj hb
    exact h ⟨a,b,hj,ha,hb⟩
  · intro h c ⟨a,b,hj,ha,hb⟩
    exact h ha b c hj hb

variable {A : Signature}

theorem Pattern.mu_unfold (M : Model A) {r} (body : Pattern A (r+1)) (η : Env M r) :
    (.mu body : Pattern A r).denote M η = body.denote M (Fin.cases ((.mu body : Pattern A r).denote M η) η) :=
  ((body.denote M).comp (insert M η)).map_lfp.symm

theorem Pattern.mu_induction (M : Model A) {r} (body : Pattern A (r+1)) (η : Env M r)
    (X : Set M.resource.carrier) (h : body.denote M (Fin.cases X η) ⊆ X) :
    (.mu body : Pattern A r).denote M η ⊆ X :=
  ((body.denote M).comp (insert M η)).lfp_le h

end Silmaril.Logic.Separation
