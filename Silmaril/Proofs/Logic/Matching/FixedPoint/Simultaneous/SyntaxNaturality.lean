module

public import Silmaril.Logic.Matching.FixedPoint.Simultaneous.Defs
public import Silmaril.Logic.Matching.FixedPoint.SortNaturality.Thms

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.Simultaneous
open CategoryTheory
open Algebraic.ManySorted (Signature)
open SortNaturality

private theorem ren_heq {S : Type} {r l : Nat}
    {P P' : Fin r → S} {Q Q' : Fin l → S}
    (hP : P = P') (hQ : Q = Q') (ρ : Ren P Q) (τ : Ren P' Q')
    (h : ∀ i, (ρ i).val = (τ i).val) : HEq ρ τ := by
  cases hP
  cases hQ
  apply heq_of_eq
  funext i
  exact Subtype.ext (h i)

/-- Both append transports and the captured head transport are retained. -/
theorem mapRen_tailRen {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l : Nat} (P : Fin (r+1) → B.sorts) (Q : Fin l → B.sorts) :
    HEq (mapRen f (tailRen P Q))
      (tailRen (f.sorts ∘ P) (f.sorts ∘ Q)) := by
  apply ren_heq (map_append f P Q)
    ((map_append f (P ∘ Fin.succ) (Fin.cases (P 0) Q)).trans
      (congrArg (append (f.sorts ∘ (P ∘ Fin.succ)))
        (SortMaps.Hom.map_cons f (P 0) Q)))
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mapRen_val, tailRen, Fin.addCases_left]
    exact Fin.cases rfl (fun _ => rfl) j
  · simp only [mapRen_val, tailRen, Fin.addCases_right]

private theorem sets_cast_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S} {s : S}
    (h : P = Q) (p : Pattern A P Γ s) :
    HEq p (h ▸ p : Pattern A Q Γ s) := by
  cases h
  rfl

private theorem renameSets_full_heq {S : Type} {A : Signature S}
    {r l k : Nat} {P P' : Fin r → S} {Q Q' : Fin l → S}
    {Γ : Fin k → S} {s : S} (hP : P = P') (hQ : Q = Q')
    (p : Pattern A P Γ s) (p' : Pattern A P' Γ s) (hp : HEq p p')
    (ρ : Ren P Q) (τ : Ren P' Q') (hρ : HEq ρ τ) :
    HEq (p.renameSets ρ) (p'.renameSets τ) := by
  cases hP
  cases hQ
  cases hp
  cases hρ
  rfl

private theorem system_heq {S : Type} {A : Signature S} {r l k : Nat}
    {P P' : Fin r → S} {Q Q' : Fin l → S} {Γ : Fin k → S}
    (hP : P = P') (hQ : Q = Q')
    (s : System A P Q Γ) (t : System A P' Q' Γ)
    (hb : ∀ i, HEq (s.body i) (t.body i)) : HEq s t := by
  cases hP
  cases hQ
  apply heq_of_eq
  cases s with
  | mk sb =>
      cases t with
      | mk tb =>
          have he : sb = tb := funext (fun i => eq_of_heq (hb i))
          cases he
          rfl

private theorem compile_heq {S : Type} {A : Signature S} {r l k : Nat}
    {P P' : Fin r → S} {Q Q' : Fin l → S} {Γ : Fin k → S}
    (hP : P = P') (hQ : Q = Q')
    (s : System A P Q Γ) (t : System A P' Q' Γ) (hs : HEq s t) (i : Fin r) :
    HEq (s.compile i) (t.compile i) := by
  cases hP
  cases hQ
  cases hs
  rfl

/-- Tail elimination commutes with sort maps as actual indexed syntax.
The heterogeneous equality records the mapped captured-head context. -/
theorem System.tail_map_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P : Fin (r+1) → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts} (s : System B.symbols P Q Γ) :
    HEq (s.tail.map f) ((s.map f).tail) := by
  apply system_heq rfl (SortMaps.Hom.map_cons f (P 0) Q)
  intro i
  exact
    (sets_cast_heq (map_append f (P ∘ Fin.succ) (Fin.cases (P 0) Q))
      (SortMaps.Hom.fixedPattern f
        ((s.body i.succ).renameSets (tailRen P Q)))).symm.trans
    ((heq_of_eq (fixedPattern_renameSets f (s.body i.succ) (tailRen P Q))).trans
      (renameSets_full_heq (map_append f P Q)
        ((map_append f (P ∘ Fin.succ) (Fin.cases (P 0) Q)).trans
          (congrArg (append (f.sorts ∘ (P ∘ Fin.succ)))
            (SortMaps.Hom.map_cons f (P 0) Q)))
        (SortMaps.Hom.fixedPattern f (s.body i.succ))
        ((s.map f).body i.succ)
        (sets_cast_heq (map_append f P Q)
          (SortMaps.Hom.fixedPattern f (s.body i.succ)))
        _ _ (mapRen_tailRen f P Q)))

private theorem sort_cast_heq {S : Type} {A : Signature S}
    {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s t : S}
    (h : s = t) (p : Pattern A P Γ s) :
    HEq (h ▸ p : Pattern A P Γ t) p := by
  cases h
  rfl

private theorem fixedPattern_sort_cast_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts}
    {s t : B.sorts} (h : s = t) (p : Pattern B.symbols P Γ s) :
    HEq (SortMaps.Hom.fixedPattern f (h ▸ p : Pattern B.symbols P Γ t))
      (SortMaps.Hom.fixedPattern f p) := by
  cases h
  rfl

private theorem setvar_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S}
    (h : P = Q) (i : Fin r) :
    HEq (.setvar i : Pattern A P Γ (P i)) (.setvar i : Pattern A Q Γ (Q i)) := by
  cases h
  rfl

private theorem replacements_full_heq {S : Type} {A : Signature S}
    {r l k : Nat} {P P' : Fin r → S} {Q Q' : Fin l → S}
    {Γ : Fin k → S} (hP : P = P') (hQ : Q = Q')
    (σ : ∀ i, Pattern A Q Γ (P i)) (τ : ∀ i, Pattern A Q' Γ (P' i))
    (hσ : ∀ i, HEq (σ i) (τ i)) : HEq σ τ := by
  cases hP
  cases hQ
  apply heq_of_eq
  funext i
  exact eq_of_heq (hσ i)

/-- Mapping the head substitution preserves every original equation and
external variable slot, even if their result sorts coincide. -/
theorem headSub_map_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P : Fin (r+1) → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts}
    (tail : ∀ i : Fin r, Pattern B.symbols (Fin.cases (P 0) Q) Γ (P i.succ))
    (target : ∀ i : Fin r,
      Pattern C.symbols (Fin.cases (f.sorts (P 0)) (f.sorts ∘ Q))
        (f.sorts ∘ Γ) (f.sorts (P i.succ)))
    (ht : ∀ i, HEq (SortMaps.Hom.fixedPattern f (tail i)) (target i)) :
    HEq (fun i => SortMaps.Hom.fixedPattern f (headSub tail i))
      (headSub (P := f.sorts ∘ P) (Q := f.sorts ∘ Q) target) := by
  apply replacements_full_heq (map_append f P Q)
    (SortMaps.Hom.map_cons f (P 0) Q)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [headSub, Fin.addCases_left]
    apply (fixedPattern_sort_cast_heq f (append_left P Q j).symm _).trans
    apply HEq.trans _ (sort_cast_heq
      (append_left (f.sorts ∘ P) (f.sorts ∘ Q) j).symm _).symm
    exact Fin.cases
      (setvar_heq (SortMaps.Hom.map_cons f (P 0) Q) 0) ht j
  · simp only [headSub, Fin.addCases_right]
    exact (fixedPattern_sort_cast_heq f (append_right P Q j).symm _).trans
      ((setvar_heq (SortMaps.Hom.map_cons f (P 0) Q) j.succ).trans
        (sort_cast_heq
          (append_right (f.sorts ∘ P) (f.sorts ∘ Q) j).symm _).symm)

private theorem substituteSets_full_heq {S : Type} {A : Signature S}
    {r l k : Nat} {P P' : Fin r → S} {Q Q' : Fin l → S}
    {Γ : Fin k → S} {s : S} (hP : P = P') (hQ : Q = Q')
    (p : Pattern A P Γ s) (p' : Pattern A P' Γ s) (hp : HEq p p')
    (σ : ∀ i, Pattern A Q Γ (P i)) (τ : ∀ i, Pattern A Q' Γ (P' i))
    (hσ : HEq σ τ) : HEq (p.substituteSets σ) (p'.substituteSets τ) := by
  cases hP
  cases hQ
  cases hp
  cases hσ
  rfl

private theorem mu_heq {S : Type} {A : Signature S} {r k : Nat}
    {P Q : Fin (r+1) → S} {Γ : Fin k → S} (h : P = Q)
    (p : Pattern A P Γ (P 0)) (q : Pattern A Q Γ (Q 0)) (hp : HEq p q) :
    HEq (Pattern.mu p) (Pattern.mu q) := by
  cases h
  cases hp
  rfl

/-- Literal dependent Bekič compiler naturality. Arbitrary sort maps change
sort witnesses and symbols, while the original finite coordinate family and
capture-avoiding native unary syntax remain intact. -/
theorem System.compile_map {B C : SortMaps.Signature} (f : B ⟶ C) :
    ∀ {r l k : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
      {Γ : Fin k → B.sorts} (s : System B.symbols P Q Γ) (i : Fin r),
      SortMaps.Hom.fixedPattern f (s.compile i) = (s.map f).compile i := by
  intro r
  induction r with
  | zero =>
      intro l k P Q Γ s i
      exact i.elim0
  | succ r ih =>
      intro l k P Q Γ s i
      let tail := s.tail.compile
      let target := (s.map f).tail.compile
      have ht : ∀ j, HEq (SortMaps.Hom.fixedPattern f (tail j)) (target j) := by
        intro j
        exact (heq_of_eq (ih s.tail j)).trans
          (compile_heq rfl (SortMaps.Hom.map_cons f (P 0) Q)
            (s.tail.map f) ((s.map f).tail) (s.tail_map_heq f) j)
      let head : Pattern B.symbols Q Γ (P 0) :=
        Pattern.mu (P' := Fin.cases (P 0) Q)
          ((s.body 0).substituteSets (headSub tail))
      let targetHead : Pattern C.symbols (f.sorts ∘ Q) (f.sorts ∘ Γ) (f.sorts (P 0)) :=
        Pattern.mu (P' := Fin.cases (f.sorts (P 0)) (f.sorts ∘ Q))
          (((s.map f).body 0).substituteSets (headSub target))
      have hh : SortMaps.Hom.fixedPattern f head = targetHead := by
        apply eq_of_heq
        apply mu_heq (SortMaps.Hom.map_cons f (P 0) Q)
        exact (heq_of_eq (fixedPattern_substituteSets f (s.body 0) (headSub tail))).trans
          (substituteSets_full_heq (map_append f P Q)
            (SortMaps.Hom.map_cons f (P 0) Q)
            (SortMaps.Hom.fixedPattern f (s.body 0)) ((s.map f).body 0)
            (sets_cast_heq (map_append f P Q) (SortMaps.Hom.fixedPattern f (s.body 0)))
            _ _ (headSub_map_heq f tail target ht))
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hh
      · change SortMaps.Hom.fixedPattern f
          ((tail j).substituteSets (Fin.cases head Pattern.setvar)) =
          (target j).substituteSets (Fin.cases targetHead Pattern.setvar)
        apply eq_of_heq
        apply (heq_of_eq (fixedPattern_substituteSets f (tail j)
          (Fin.cases head Pattern.setvar))).trans
        apply substituteSets_full_heq (SortMaps.Hom.map_cons f (P 0) Q) rfl
          (SortMaps.Hom.fixedPattern f (tail j)) (target j) (ht j)
        apply replacements_full_heq (SortMaps.Hom.map_cons f (P 0) Q) rfl
        intro j
        exact Fin.cases (heq_of_eq hh) (fun _ => HEq.rfl) j

end Silmaril.Logic.Matching.FixedPoint.Simultaneous
