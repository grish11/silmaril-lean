module

public import Silmaril.Semantics.ConcurrentTrace.TraceMonoid.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.TraceMonoid

public section

namespace Silmaril.Semantics.ConcurrentTrace.TraceMonoid

universe u v w

variable {A : Type u} {B : Type v} {I : A → A → Prop} {J : B → B → Prop}

/-- Homomorphisms out of a trace monoid are determined by their values on letters. -/
theorem hom_ext {M : Type w} [Monoid M] {f g : Trace I →* M}
    (h : ∀ a, f (singleton I a) = g (singleton I a)) : f = g :=
  (congruence I).hom_ext (FreeMonoid.hom_eq h)

@[simp] theorem map_ofWord (f : A → B) (h : ∀ ⦃a b⦄, I a b → J (f a) (f b)) (word : List A) :
    map f h (ofWord I word) = ofWord J (word.map f) :=
  Proofs.Semantics.ConcurrentTrace.TraceMonoid.map_ofWord f h word

/-- Distinct letters in a symmetric presentation commute exactly when independent. -/
theorem singleton_mul_comm_iff (hsymm : Std.Symm I) (a b : A) :
    singleton I a * singleton I b = singleton I b * singleton I a ↔ a = b ∨ I a b :=
  Proofs.Semantics.ConcurrentTrace.TraceMonoid.singleton_mul_comm_iff hsymm a b

/-- An equivalence of alphabets that preserves and reflects independence induces
an equivalence of their trace monoids. -/
@[expose] def mapEquiv (e : A ≃ B) (h : ∀ a b, J (e a) (e b) ↔ I a b) : Trace I ≃* Trace J :=
  let forward := map e (fun {a b} => (h a b).mpr)
  let backward := map e.symm (fun {a b} hab => (h (e.symm a) (e.symm b)).mp (by simpa using hab))
  forward.toMulEquiv backward
    (hom_ext fun a => by simp [forward, backward])
    (hom_ext fun a => by simp [forward, backward])

@[simp] theorem mapEquiv_ofWord (e : A ≃ B) (h : ∀ a b, J (e a) (e b) ↔ I a b) (word : List A) :
    mapEquiv e h (ofWord I word) = ofWord J (word.map e) :=
  map_ofWord (I := I) e (fun {a b} => (h a b).mpr) word

end Silmaril.Semantics.ConcurrentTrace.TraceMonoid
