module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms

/-! # Function-level laws for examples on types -/

@[expose] public section

namespace Silmaril.Calco2019.Examples.TypeKleisli

universe u

variable (m : Type u → Type u) [Monad m]

/-- Definition 6 in the function presentation of a type monad. -/
structure Guard where
  holds {X Y Z : Type u} : (X → m (Y ⊕ Z)) → Prop
  trivial {X Y Z : Type u} (f : X → m Y) :
    holds (f >=> Elgot.liftPure (Sum.inl : Y → Y ⊕ Z))
  parallel {X Y V W : Type u} {f : X → m (V ⊕ W)} {g : Y → m (V ⊕ W)} :
    holds f → holds g → holds (Sum.elim f g)
  compose {X Y Z V W : Type u} {f : X → m (Y ⊕ Z)} {g : Y → m (V ⊕ W)}
    (h : Z → m (V ⊕ W)) : holds f → holds g → holds (f >=> Sum.elim g h)

def reassociate {Y Z W : Type u} : (Y ⊕ Z) ⊕ W → Y ⊕ (Z ⊕ W)
  | .inl (.inl y) => .inl y
  | .inl (.inr z) => .inr (.inl z)
  | .inr w => .inr (.inr w)

/-- The fixpoint, naturality, codiagonal, and pure uniformity laws in function form. -/
structure Iteration (G : Guard m) where
  run {X Y : Type u} (f : X → m (Y ⊕ X)) : G.holds f → X → m Y
  fixpoint {X Y : Type u} (f : X → m (Y ⊕ X)) (hf : G.holds f) :
    f >=> Sum.elim pure (run f hf) = run f hf
  naturality {X Y Z : Type u} (f : X → m (Y ⊕ X)) (g : Y → m Z) (hf : G.holds f)
    (hg : G.holds (Elgot.mapReturn f g)) :
    run (Elgot.mapReturn f g) hg = run f hf >=> g
  codiagonal {X Y : Type u} (f : X → m ((Y ⊕ X) ⊕ X))
    (hn : G.holds (f >=> Elgot.liftPure reassociate))
    (hi : G.holds f) (ho : G.holds (run f hi)) (hm : G.holds (Elgot.flattenBody f)) :
    run (Elgot.flattenBody f) hm = run (run f hi) ho
  uniformity {X Y Z : Type u} (f : X → m (Y ⊕ X)) (g : Z → m (Y ⊕ Z))
    (h : Z → X) (hf : G.holds f) (hg : G.holds g) :
    f ∘ h = g >=> Elgot.liftPure (Sum.map id h) → run f hf ∘ h = run g hg

/-- Unique guarded solutions in the function presentation. -/
def Guard.HasUniqueFixpoints (G : Guard m) : Prop :=
  ∀ {X Y : Type u} (f : X → m (Y ⊕ X)), G.holds f →
    ∃! g, f >=> Sum.elim pure g = g

end Silmaril.Calco2019.Examples.TypeKleisli
