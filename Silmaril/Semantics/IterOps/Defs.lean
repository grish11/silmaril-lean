module

public import Silmaril.Semantics.Elgot.Thms

/-!
# Premonoidal Elgot structure on a family of hom types, and its transfer

`IterOps H` equips a family of hom types `H A B` (indexed by value types, i.e.
typed interfaces) with:

* identity, composition (diagrammatic) and pure maps from functions;
* copairing of a coproduct source (control with several entries);
* Elgot iteration `H A (B ⊕ A) → H A B` (`inl` exits, `inr` loops);
* left whiskering `H A B → H (C × A) (C × B)`, the premonoidal tensor with a
  passive context. Effects stay ordered: no naturality in both arguments is
  assumed, only centrality of pure maps.

`IterOps.Lawful` collects the laws:

* category laws;
* pure maps form a functor, and copairing satisfies its coproduct equations
  with the pure injections;
* the complete Elgot laws: fixpoint, naturality, codiagonal, and uniformity
  along pure maps;
* the premonoidal laws: whiskering preserves identities and composition,
  whiskering a pure map is pure, and pure maps are central, i.e. they commute
  with any whiskered map.

`Silmaril.Semantics.IterOps.Thms` proves the following:

* the Kleisli family of any lawful Elgot monad (`kleisliOps m`) is lawful;
* **transfer**: if `F : H → H'` is faithful (injective on every hom type) and
  preserves every operation, then `Lawful H'` implies `Lawful H`.

Transfer is the structure-transfer strategy for concrete code. Define the
concrete operations, the semantic functor, preservation and faithfulness on
the chosen quotient, and the laws follow. This does not by itself make the
concrete homs closed under the operations: the concrete operations must exist
and `F` must preserve them, which is part of the hypothesis.
-/

@[expose] public section

namespace Silmaril.IterOps

universe u w

/-- Premonoidal Elgot operations on a family of hom types. -/
structure Ops (H : Type u → Type u → Type w) where
  /-- Identity. -/
  id (A : Type u) : H A A
  /-- Composition, diagrammatic order. -/
  comp {A B C : Type u} : H A B → H B C → H A C
  /-- A pure map from a function. -/
  pure {A B : Type u} : (A → B) → H A B
  /-- Copairing out of a coproduct. -/
  case {A B C : Type u} : H A C → H B C → H (A ⊕ B) C
  /-- Elgot iteration. -/
  iter {A B : Type u} : H A (B ⊕ A) → H A B
  /-- Left whiskering by a passive context. -/
  whisker {A B : Type u} (C : Type u) : H A B → H (C × A) (C × B)

namespace Ops

variable {H : Type u → Type u → Type w} (o : Ops H)

/-- The laws of a premonoidal Elgot structure (see the module docstring). -/
structure Lawful : Prop where
  id_comp {A B : Type u} (f : H A B) : o.comp (o.id A) f = f
  comp_id {A B : Type u} (f : H A B) : o.comp f (o.id B) = f
  comp_assoc {A B C D : Type u} (f : H A B) (g : H B C) (h : H C D) :
    o.comp (o.comp f g) h = o.comp f (o.comp g h)
  pure_id (A : Type u) : o.pure (fun a : A => a) = o.id A
  pure_comp {A B C : Type u} (f : A → B) (g : B → C) :
    o.comp (o.pure f) (o.pure g) = o.pure (g ∘ f)
  inl_case {A B C : Type u} (f : H A C) (g : H B C) :
    o.comp (o.pure Sum.inl) (o.case f g) = f
  inr_case {A B C : Type u} (f : H A C) (g : H B C) :
    o.comp (o.pure Sum.inr) (o.case f g) = g
  case_comp {A B C D : Type u} (f : H A C) (g : H B C) (h : H C D) :
    o.comp (o.case f g) h = o.case (o.comp f h) (o.comp g h)
  fixpoint {A B : Type u} (f : H A (B ⊕ A)) :
    o.iter f = o.comp f (o.case (o.id B) (o.iter f))
  naturality {A B C : Type u} (f : H A (B ⊕ A)) (g : H B C) :
    o.comp (o.iter f) g =
      o.iter (o.comp f (o.case (o.comp g (o.pure Sum.inl)) (o.pure Sum.inr)))
  codiagonal {A B : Type u} (f : H A ((B ⊕ A) ⊕ A)) :
    o.iter (o.iter f) = o.iter (o.comp f (o.pure (Sum.elim _root_.id Sum.inr)))
  uniformity {A B C : Type u} (f : H A (B ⊕ A)) (g : H C (B ⊕ C)) (h : A → C)
    (comm : o.comp f (o.pure (Sum.map _root_.id h)) = o.comp (o.pure h) g) :
    o.iter f = o.comp (o.pure h) (o.iter g)
  whisker_id (C A : Type u) : o.whisker C (o.id A) = o.id (C × A)
  whisker_comp {A B D : Type u} (C : Type u) (f : H A B) (g : H B D) :
    o.whisker C (o.comp f g) = o.comp (o.whisker C f) (o.whisker C g)
  whisker_pure {A B : Type u} (C : Type u) (f : A → B) :
    o.whisker C (o.pure f) = o.pure (Prod.map _root_.id f)
  pure_central {A B C D : Type u} (h : C → D) (f : H A B) :
    o.comp (o.whisker C f) (o.pure (Prod.map h _root_.id)) =
      o.comp (o.pure (Prod.map h _root_.id)) (o.whisker D f)

end Ops

/-- The Kleisli operations of a monad with an iteration operator. -/
def kleisliOps (m : Type u → Type u) [Monad m] [Silmaril.Elgot.Iterate m] :
    Ops (fun A B => A → m B) where
  id _ := fun a => Pure.pure a
  comp f g := fun a => f a >>= g
  pure f := fun a => Pure.pure (f a)
  case f g := Sum.elim f g
  iter f := Silmaril.Elgot.iter f
  whisker _ f := fun p => (fun b => (p.1, b)) <$> f p.2

/-- A faithful, operation-preserving map of hom families. -/
structure Hom {H H' : Type u → Type u → Type w} (o : Ops H) (o' : Ops H') where
  /-- The map on homs. -/
  map {A B : Type u} : H A B → H' A B
  /-- Faithfulness: injective on every hom type. -/
  faithful {A B : Type u} : Function.Injective (map (A := A) (B := B))
  map_id (A : Type u) : map (o.id A) = o'.id A
  map_comp {A B C : Type u} (f : H A B) (g : H B C) : map (o.comp f g) = o'.comp (map f) (map g)
  map_pure {A B : Type u} (f : A → B) : map (o.pure f) = o'.pure f
  map_case {A B C : Type u} (f : H A C) (g : H B C) : map (o.case f g) = o'.case (map f) (map g)
  map_iter {A B : Type u} (f : H A (B ⊕ A)) : map (o.iter f) = o'.iter (map f)
  map_whisker {A B : Type u} (C : Type u) (f : H A B) : map (o.whisker C f) = o'.whisker C (map f)

end Silmaril.IterOps
