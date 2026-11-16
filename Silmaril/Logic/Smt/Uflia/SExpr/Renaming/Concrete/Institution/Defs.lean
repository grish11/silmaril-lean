module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Action.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- The normalizing concrete institution has genuine coherent name-map arrows,
actual accepted byte-representative quotient sentences, and the existing models. -/
noncomputable def plain : Plain EnvironmentSignature where
  Sen S := Sentence S.environment
  map f s := Sentence.map f s
  map_id _ := Sentence.map_id
  map_comp := Sentence.map_comp
  Mod S := Uflia.Model S.environment.signature
  reduct f M := Uflia.Model.reduct f.abstract M
  reduct_id _ := Uflia.Model.reduct_id
  reduct_comp f g M := Uflia.Model.reduct_comp f.abstract g.abstract M
  Sat M s := Holds M s
  sat_map := holds_map

noncomputable abbrev institution := plain.toInst

/-- Checked prefixes retain their actual declaration-decoding witnesses while
using the same genuine symbol maps and concrete normalizing sentence action. -/
noncomputable def declarationPlain : Plain PrefixSignature where
  Sen S := Sentence S.prefix.environment
  map f s := Sentence.map f s
  map_id _ := Sentence.map_id
  map_comp := Sentence.map_comp
  Mod S := Uflia.Model S.prefix.environment.signature
  reduct f M := Uflia.Model.reduct f.abstract M
  reduct_id _ := Uflia.Model.reduct_id
  reduct_comp f g M := Uflia.Model.reduct_comp f.abstract g.abstract M
  Sat M s := Holds M s
  sat_map := holds_map

noncomputable abbrev declarationInstitution := declarationPlain.toInst

noncomputable abbrev room (E : Environment) := plain.room ⟨E⟩
noncomputable abbrev declarationRoom (checked : DeclarationPrefix) := declarationPlain.room ⟨checked⟩

/-- Actual representative decoding is natural with respect to arbitrary
coherent name maps and their actual profile-preserving abstract operation maps. -/
noncomputable def decodeComorphism : Comorphism institution (Uflia.institution String) :=
  Comorphism.ofPlain environmentFunctor (fun _ => Sentence.decode) (fun _ => id)
    (fun _ _ _ => Iff.rfl)
    (fun f s => Sentence.decode_map f s)
    (fun _ _ => rfl)

/-- The decoder comorphism retains checked declaration prefixes in its source
signature category; its abstract signature functor forgets their evidence. -/
noncomputable def declarationDecodeComorphism :
    Comorphism declarationInstitution (Uflia.institution String) :=
  Comorphism.ofPlain prefixAbstractFunctor (fun _ => Sentence.decode) (fun _ => id)
    (fun _ _ _ => Iff.rfl)
    (fun f s => Sentence.decode_map f s)
    (fun _ _ => rfl)

/-- Forgetting prefix evidence preserves actual byte-backed sentences and models. -/
noncomputable def prefixForgetComorphism : Comorphism declarationInstitution institution :=
  Comorphism.ofPlain prefixFunctor (fun _ => id) (fun _ => id)
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
