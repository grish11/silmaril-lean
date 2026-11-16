module

public import Silmaril.Proofs.Logic.Matching.FixedPoint.Simultaneous

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint.Simultaneous
open CategoryTheory
open Algebraic.ManySorted (Signature)

private theorem env_cast_apply {S : Type} {A : Signature S} (M : Model A)
    {r : Nat} {P Q : Fin r → S} (h : P = Q) (η : SetEnv A M P) (i : Fin r) :
    HEq ((h ▸ η : SetEnv A M Q) i) (η i) := by
  cases h
  rfl

private theorem denote_sets_cast {S : Type} {A : Signature S} (M : Model A)
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S} {s : S} (h : P = Q)
    (p : Pattern A P Γ s) (v : ObjEnv A M Γ) (η : SetEnv A M Q) :
    (h ▸ p : Pattern A Q Γ s).denote M v η =
      p.denote M v (h.symm ▸ η) := by
  cases h
  rfl

/-- The simultaneous operator commutes with genuine sort-changing reduct,
including maps that identify sorts. The dependent coordinate indices are fixed. -/
theorem System.operator_map {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts} (s : System B.symbols P Q Γ)
    (M : Model C.symbols) (v : ObjEnv B.symbols (SortMaps.Hom.reduct f M) Γ)
    (η : SetEnv B.symbols (SortMaps.Hom.reduct f M) Q) :
    (s.map f).operator M v η = s.operator (SortMaps.Hom.reduct f M) v η := by
  apply OrderHom.ext
  funext X i
  change ((map_append f P Q) ▸ SortMaps.Hom.fixedPattern f (s.body i)).denote
    M v (joinEnv M η X) = _
  rw [denote_sets_cast, SortMaps.Hom.denote_fixedPattern]
  apply congrArg (fun ζ => (s.body i).denote (SortMaps.Hom.reduct f M) v ζ)
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    apply eq_of_heq
    exact (env_cast_apply M (map_append f P Q).symm (joinEnv M η X)
      (Fin.castAdd l j)).trans
      ((joinEnv_left_heq M η X j).trans
        (joinEnv_left_heq (SortMaps.Hom.reduct f M) η X j).symm)
  · intro j
    apply eq_of_heq
    exact (env_cast_apply M (map_append f P Q).symm (joinEnv M η X)
      (Fin.natAdd r j)).trans
      ((joinEnv_right_heq M η X j).trans
        (joinEnv_right_heq (SortMaps.Hom.reduct f M) η X j).symm)

theorem System.denote_map {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts} (s : System B.symbols P Q Γ)
    (M : Model C.symbols) (v : ObjEnv B.symbols (SortMaps.Hom.reduct f M) Γ)
    (η : SetEnv B.symbols (SortMaps.Hom.reduct f M) Q) :
    (s.map f).denote M v η = s.denote (SortMaps.Hom.reduct f M) v η :=
  congrArg (fun op => op.lfp) (s.operator_map f M v η)

/-- Semantic naturality of the actual scalar compiled patterns.
This theorem does not assert literal equality of syntax trees. -/
theorem System.compile_denote_map {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts} (s : System B.symbols P Q Γ)
    (M : Model C.symbols) (v : ObjEnv B.symbols (SortMaps.Hom.reduct f M) Γ)
    (η : SetEnv B.symbols (SortMaps.Hom.reduct f M) Q) (i : Fin r) :
    ((s.map f).compile i).denote M v η =
      (SortMaps.Hom.fixedPattern f (s.compile i)).denote M v η := by
  rw [SortMaps.Hom.denote_fixedPattern]
  have hm := congrFun ((s.map f).compile_correct M v η) i
  have hs := congrFun (s.compile_correct (SortMaps.Hom.reduct f M) v η) i
  exact hm.trans ((congrFun (s.denote_map f M v η) i).trans hs.symm)

end Silmaril.Logic.Matching.FixedPoint.Simultaneous
