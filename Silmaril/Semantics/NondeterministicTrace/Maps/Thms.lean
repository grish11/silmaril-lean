module

public import Silmaril.Semantics.NondeterministicTrace.Finite.Thms
public import Mathlib.Order.Setoid.Basic
import Silmaril.Proofs.Semantics.NondeterministicTrace.Maps

public section

namespace Silmaril.Semantics.NondeterministicTrace.Finite

open Silmaril.Elgot

universe u

variable {W V A B : Type u} [Monoid W] [Monoid V] (h : W →* V)

theorem mem_mapLog {p : Finite W A} {a : A} {v : V} :
    (a, v) ∈ (mapLog h p).outcomes ↔ ∃ w, (a, w) ∈ p.outcomes ∧ h w = v :=
  Proofs.Semantics.NondeterministicTrace.Maps.mem_mapLog h

@[simp] theorem mapLog_pure (a : A) : mapLog h (pure a) = (pure a : Finite V A) :=
  Proofs.Semantics.NondeterministicTrace.Maps.mapLog_pure h a

theorem mapLog_bind (p : Finite W A) (k : A → Finite W B) :
    mapLog h (p >>= k) = mapLog h p >>= fun a => mapLog h (k a) :=
  Proofs.Semantics.NondeterministicTrace.Maps.mapLog_bind h p k

/-- Interpreting logs commutes with complete Elgot iteration. -/
theorem mapLog_iter (f : A → Finite W (B ⊕ A)) (a : A) :
    mapLog h (iter f a) = iter (fun next => mapLog h (f next)) a :=
  Proofs.Semantics.NondeterministicTrace.Maps.mapLog_iter h f a

theorem mapLog_injective (hh : Function.Injective h) :
    Function.Injective (mapLog h : Finite W A → Finite V A) :=
  Proofs.Semantics.NondeterministicTrace.Maps.mapLog_injective h hh

theorem mapLog_surjective (hh : Function.Surjective h) :
    Function.Surjective (mapLog h : Finite W A → Finite V A) :=
  Proofs.Semantics.NondeterministicTrace.Maps.mapLog_surjective h hh

/-- An injective interpretation gives an iteration-preserving monad embedding. -/
def logEmbedding (hh : Function.Injective h) : Embedding (Finite W) (Finite V) where
  map := mapLog h
  injective := fun {_} {_ _} eq => mapLog_injective h hh eq
  map_pure := mapLog_pure h
  map_bind := mapLog_bind h
  map_iter := mapLog_iter h

@[simp] theorem logEmbedding_map (hh : Function.Injective h) (p : Finite W A) :
    (logEmbedding h hh).map p = mapLog h p := by rfl

/-- A surjective log interpretation presents the target by the kernel quotient. -/
noncomputable def logQuotient (hh : Function.Surjective h) :
    Quotient (Setoid.ker (mapLog h : Finite W A → Finite V A)) ≃ Finite V A :=
  Setoid.quotientKerEquivOfSurjective (mapLog h) (mapLog_surjective h hh)

@[simp] theorem logQuotient_mk (hh : Function.Surjective h) (p : Finite W A) :
    logQuotient h hh (Quotient.mk _ p) = (mapLog h p : Finite V A) := by rfl

end Silmaril.Semantics.NondeterministicTrace.Finite
