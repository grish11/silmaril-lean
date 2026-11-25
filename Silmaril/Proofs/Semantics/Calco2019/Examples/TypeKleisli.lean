module

public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.TypeKleisli.Proofs

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

local notation "T" => ofTypeMonad m
local notation "Q" => typeCoproducts.kleisli T
local notation "J" => Kleisli.Adjunction.toKleisli T

variable {X Y Z W : Type u}

private theorem comp (f : X → m Y) (g : Y → m Z) :
    computation m f ≫ computation m g = computation m (f >=> g) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  exact Kleisli.Type.comp_of_eq_kleisliRight m _ _

private theorem pureComp (f : X → Y) (g : Y → m Z) :
    computation m (Elgot.liftPure f) ≫ computation m g = computation m (g ∘ f) := by
  rw [comp]
  apply congrArg (computation m)
  funext x
  exact pure_bind (f x) g

private theorem desc (f : X → m Z) (g : Y → m Z) :
    (Q).desc (computation m f) (computation m g) = computation m (Sum.elim f g) := by
  apply (Q).hom_ext
  · rw [(Q).inl_desc]
    exact (pureComp m Sum.inl (Sum.elim f g)).symm
  · rw [(Q).inr_desc]
    exact (pureComp m Sum.inr (Sum.elim f g)).symm

private theorem mapReturn (g : Y → m Z) :
    (Q).map (computation m g) (𝟙 ((J).obj X)) =
      computation m (Sum.elim (g >=> Elgot.liftPure Sum.inl) (Elgot.liftPure Sum.inr)) := by
  rw [Coproducts.map, Category.id_comp]
  change (Q).desc (computation m g ≫ computation m (Elgot.liftPure Sum.inl))
    (computation m (Elgot.liftPure Sum.inr)) = _
  rw [comp, desc]

private theorem merge :
    ((Q).merge : (Q).sum ((Q).sum ((J).obj Y) ((J).obj X)) ((J).obj X) ⟶ (Q).sum ((J).obj Y) ((J).obj X)) =
      computation m (Elgot.liftPure Elgot.flatten) := by
  apply (Q).hom_ext
  · rw [Coproducts.merge, (Q).inl_desc]
    exact (pureComp m Sum.inl (Elgot.liftPure Elgot.flatten)).symm
  · rw [Coproducts.merge, (Q).inr_desc]
    exact (pureComp m Sum.inr (Elgot.liftPure Elgot.flatten)).symm

private theorem assoc :
    ((Q).assoc : (Q).sum ((Q).sum ((J).obj Y) ((J).obj Z)) ((J).obj W) ⟶
      (Q).sum ((J).obj Y) ((Q).sum ((J).obj Z) ((J).obj W))) =
      computation m (Elgot.liftPure reassociate) := by
  let l : Y → Y ⊕ (Z ⊕ W) := Sum.inl
  let ml : Z → Z ⊕ W := Sum.inl
  let mr : W → Z ⊕ W := Sum.inr
  let r : Z ⊕ W → Y ⊕ (Z ⊕ W) := Sum.inr
  change (Q).desc ((Q).desc (computation m (Elgot.liftPure l))
    (computation m (Elgot.liftPure ml) ≫ computation m (Elgot.liftPure r)))
    (computation m (Elgot.liftPure mr) ≫ computation m (Elgot.liftPure r)) = _
  rw [pureComp, pureComp, desc, desc]
  apply congrArg (computation m)
  funext x
  rcases x with (y | z) | w <;> rfl

private theorem mapState (h : X → Z) :
    (Q).map (𝟙 ((J).obj Y)) ((J).map (↾h)) =
      computation m (Elgot.liftPure (Sum.map id h)) := by
  apply (Q).hom_ext
  · rw [Coproducts.map, (Q).inl_desc, Category.id_comp]
    exact (pureComp m Sum.inl (Elgot.liftPure (Sum.map id h))).symm
  · rw [Coproducts.map, (Q).inr_desc]
    exact (pureComp m h (Elgot.liftPure Sum.inr)).trans
      (pureComp m (Sum.inr : X → Y ⊕ X) (Elgot.liftPure (Sum.map id h))).symm

noncomputable def guard (G : Guard m) : MonadGuardedness typeCoproducts T where
  guarded f := G.holds f.of
  trivial {X Y Z} f := by
    obtain ⟨A⟩ := X
    obtain ⟨B⟩ := Y
    obtain ⟨C⟩ := Z
    change G.holds (computation m f.of ≫ computation m (Elgot.liftPure (Sum.inl : B → B ⊕ C))).of
    rw [comp]
    exact G.trivial f.of
  parallel {X Y V W} {f g} hf hg := by
    cases X; cases Y; cases V; cases W
    change G.holds ((Q).desc (computation m f.of) (computation m g.of)).of
    rw [desc]
    exact G.parallel hf hg
  compose {X Y Z V W} {f g} h hf hg := by
    cases X; cases Y; cases Z; cases V; cases W
    change G.holds (computation m f.of ≫ (Q).desc (computation m g.of) (computation m h.of)).of
    rw [desc, comp]
    exact G.compose h.of hf hg

theorem guard_iff (G : Guard m) (f : X → m (Y ⊕ Z)) :
    (guard m G).guarded (computation m f) ↔ G.holds f := by unfold guard; rfl

variable {m} {G : Guard m} (I : Iteration m G)

private theorem fix (X Y : Kleisli T) (f : X ⟶ (Q).sum Y X)
    (hf : (guard m G).guarded f) :
    f ≫ (Q).desc (𝟙 Y) (computation m (I.run f.of hf)) = computation m (I.run f.of hf) := by
  cases X; cases Y
  change computation m f.of ≫ (Q).desc (computation m pure) (computation m (I.run f.of hf)) = _
  rw [desc, comp]
  exact congrArg (computation m) (I.fixpoint f.of hf)

noncomputable def fixpoints : (guard m G).Fixpoints where
  iterate f hf := computation m (I.run f.of hf)
  fixpoint f hf := fix I _ _ f hf

private theorem run_congr {X Y : Kleisli T} {a b : X ⟶ (Q).sum Y X}
    (h : a = b) (ha : (guard m G).guarded a) (hb : (guard m G).guarded b) :
    (fixpoints I).iterate a ha = (fixpoints I).iterate b hb := by
  subst b
  rfl

private theorem natural (X Y Z : Kleisli T) (f : X ⟶ (Q).sum Y X) (g : Y ⟶ Z)
    (hf : (guard m G).guarded f) (hg : (guard m G).guarded (f ≫ (Q).map g (𝟙 X))) :
    (fixpoints I).iterate (f ≫ (Q).map g (𝟙 X)) hg = (fixpoints I).iterate f hf ≫ g := by
  obtain ⟨A⟩ := X
  obtain ⟨B⟩ := Y
  obtain ⟨C⟩ := Z
  let body : A → m (B ⊕ A) := f.of
  let after : B → m C := g.of
  have he : f ≫ (Q).map g (𝟙 _) = computation m (Elgot.mapReturn body after) := by
    change computation m body ≫ (Q).map (computation m after) (𝟙 ((J).obj A)) = _
    rw [mapReturn m (X := A) after, comp]
    rfl
  have hg' : (guard m G).guarded (computation m (Elgot.mapReturn body after)) := he ▸ hg
  refine (run_congr I he hg hg').trans ?_
  change computation m (I.run (Elgot.mapReturn body after) hg') =
    computation m (I.run body hf) ≫ computation m after
  rw [comp]
  exact congrArg (computation m) (I.naturality body after hf hg')

private theorem diagonal (X Y : Kleisli T) (f : X ⟶ (Q).sum ((Q).sum Y X) X)
    (hn : (guard m G).nested f) (hi : (guard m G).guarded f)
    (ho : (guard m G).guarded ((fixpoints I).iterate f hi))
    (hm : (guard m G).guarded (f ≫ (Q).merge)) :
    (fixpoints I).iterate (f ≫ (Q).merge) hm = (fixpoints I).iterate ((fixpoints I).iterate f hi) ho := by
  obtain ⟨A⟩ := X
  obtain ⟨B⟩ := Y
  let body : A → m ((B ⊕ A) ⊕ A) := f.of
  change (guard m G).guarded (computation m body ≫ (Q).assoc) at hn
  rw [assoc m (Y := B) (Z := A) (W := A), comp] at hn
  have he : f ≫ (Q).merge = computation m (Elgot.flattenBody body) := by
    change computation m body ≫ (Q).merge = _
    rw [merge m (X := A) (Y := B), comp]
    rfl
  have hm' : (guard m G).guarded (computation m (Elgot.flattenBody body)) := he ▸ hm
  refine (run_congr I he hm hm').trans ?_
  change computation m (I.run (Elgot.flattenBody body) hm') =
    computation m (I.run (I.run body hi) ho)
  exact congrArg (computation m) (I.codiagonal body hn hi ho hm')

private theorem uniform : (fixpoints I).Uniform J := by
  intro X Z Y f g h hf hg comm
  obtain ⟨B⟩ := Y
  let f' : X → m (B ⊕ X) := f.of
  let g' : Z → m (B ⊕ Z) := g.of
  change computation m (Elgot.liftPure (⇑h)) ≫ computation m f' =
    computation m g' ≫ (Q).map (𝟙 ((J).obj B)) ((J).map (↾(⇑h))) at comm
  rw [mapState m (Y := B) (⇑h), pureComp, comp] at comm
  have he := congrArg (fun q : (J).obj Z ⟶ (J).obj (B ⊕ X) => ⇑q.of) comm
  change computation m (Elgot.liftPure (⇑h)) ≫ computation m (I.run f' hf) =
    computation m (I.run g' hg)
  rw [pureComp]
  exact congrArg (computation m) (I.uniformity f' g' (⇑h) hf hg he)

noncomputable def assemble : GuardedElgotMonad typeCoproducts where
  monad := T
  guard := guard m G
  iteration := {
    toFixpoints := fixpoints I
    naturalCodiagonal := ⟨fun f g hf hg => natural I _ _ _ f g hf hg,
      fun f hn hi ho hm => diagonal I _ _ f hn hi ho hm⟩
    dinaturality := (fixpoints I).dinaturality_of_uniform
      (typeCoproducts.kleisliPreservesSelected T) (by intro K; cases K; exact ⟨_, rfl⟩)
      ⟨fun f g hf hg => natural I _ _ _ f g hf hg, fun f hn hi ho hm => diagonal I _ _ f hn hi ho hm⟩
      (uniform I) }
  uniformity := uniform I

private theorem computation_fix_iff (f : X → m (Y ⊕ X)) (g : X → m Y) :
    Guardedness.IsFixpoint (P := Q) (computation m f) (computation m g) ↔
      f >=> Sum.elim pure g = g := by
  unfold Guardedness.IsFixpoint
  change computation m f ≫ (Q).desc (computation m pure) (computation m g) =
    computation m g ↔ _
  rw [desc, comp]
  exact ⟨fun e => congrArg
    (fun k : Kleisli.mk T X ⟶ Kleisli.mk T Y => (show X → m Y from k.of)) e,
    congrArg (computation m)⟩

theorem iterative_iff (G : Guard m) : (guard m G).Iterative ↔ G.HasUniqueFixpoints := by
  constructor
  · intro h X Y f hf
    obtain ⟨g, hg, hu⟩ := h (computation m f) ((guard_iff m G f).2 hf)
    let observe (k : Kleisli.mk T X ⟶ Kleisli.mk T Y) : X → m Y := k.of
    refine ⟨observe g, (computation_fix_iff f (observe g)).1 hg, fun k hk => ?_⟩
    exact congrArg observe (hu (computation m k) ((computation_fix_iff f k).2 hk))
  · intro h X Y f hf
    obtain ⟨A⟩ := X
    obtain ⟨B⟩ := Y
    let body : A → m (B ⊕ A) := f.of
    obtain ⟨g, hg, hu⟩ := h body hf
    exact ⟨computation m g, (computation_fix_iff body g).2 hg, fun k hk =>
      congrArg (computation m) (hu k.of ((computation_fix_iff body k.of).1 hk))⟩

end Silmaril.Calco2019.Examples.TypeKleisli.Proofs
