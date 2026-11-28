module

public import Silmaril.Semantics.NondeterministicTrace.Maps.Thms
public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
import Silmaril.Proofs.Semantics.NondeterministicTrace.Tagged

/-! # Complete Elgot iteration of nondeterministic trace observations -/

public section

namespace Silmaril.Semantics.NondeterministicTrace

open Silmaril.Elgot Silmaril.Calco2019

universe u

/-- Complete Elgot iteration for finite successful observations. -/
noncomputable def finiteElgot (W : Type u) [Monoid W] : GuardedElgotMonad typeCoproducts.{u} :=
  ofLawfulMonad (Finite W)

/-- Complete Elgot iteration for finite returns and explicitly tagged incomplete branches. -/
noncomputable def taggedElgot (W T : Type u) [Monoid W] : GuardedElgotMonad typeCoproducts.{u} :=
  ofLawfulMonad (Tagged W T)

theorem finite_isElgot (W : Type u) [Monoid W] : (finiteElgot W).IsElgot :=
  ofLawfulMonad_isElgot (Finite W)

theorem tagged_isElgot (W T : Type u) [Monoid W] : (taggedElgot W T).IsElgot :=
  ofLawfulMonad_isElgot (Tagged W T)

namespace Tagged

variable {W V T A B : Type u}

@[simp] theorem outcomes_ofOutcomes (s : Set (Except T A × W)) :
    outcomes (ofOutcomes s) = s := rfl

theorem outcomes_injective : Function.Injective (outcomes : Tagged W T A → Set (Except T A × W)) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.outcomes_injective

variable [Monoid W]

/-- An incomplete branch survives sequencing. Only a successful branch can supply
a value to the continuation. -/
theorem mem_bind {p : Tagged W T A} {k : A → Tagged W T B} {r : Except T B} {w : W} :
    (r, w) ∈ outcomes (p >>= k) ↔
      (∃ t, r = .error t ∧ (.error t, w) ∈ p.outcomes) ∨
      ∃ a u v, (.ok a, u) ∈ p.outcomes ∧ (r, v) ∈ (k a).outcomes ∧ u * v = w :=
  Proofs.Semantics.NondeterministicTrace.Tagged.mem_bind

/-- Iteration reports a finite run ending at a return or a supplied incomplete observation. -/
theorem mem_iter (f : A → Tagged W T (B ⊕ A)) (a : A) (r : Except T B) (w : W) :
    (r, w) ∈ outcomes (iter f a) ↔ Finite.Runs (Elgot.ExceptT.body f) a r w := by
  change (r, w) ∈ Finite.outcomes (iter f a).run ↔ _
  rw [Elgot.ExceptT.run_iter, Finite.mem_iter]

theorem unfold_eq_bind (f : A → Tagged W T (B ⊕ A)) (k : A → Set (Except T B × W)) (a : A) :
    Finite.unfoldLoop (Elgot.ExceptT.body f) k a =
      outcomes (f a >>= Sum.elim pure (fun next => ofOutcomes (k next))) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.unfold_eq_bind f k a

/-- Tagged iteration is still a least fixed point in the pointwise inclusion order. -/
theorem iter_eq_lfp (f : A → Tagged W T (B ⊕ A)) :
    (fun a => outcomes (iter f a)) = (Finite.unfoldLoop (Elgot.ExceptT.body f)).lfp :=
  Finite.iter_eq_lfp (Elgot.ExceptT.body f)

theorem outcomes_includeResults (p : Finite W A) :
    outcomes (includeResults p : Tagged W T A) =
      Prod.map (Except.ok : A → Except T A) id '' p.outcomes :=
  Proofs.Semantics.NondeterministicTrace.Tagged.outcomes_includeResults p

/-- Including a finite-result loop as a tagged computation preserves its iteration. -/
theorem includeResults_iter (f : A → Finite W (B ⊕ A)) (a : A) :
    includeResults (iter f a) = (iter (fun next => includeResults (f next)) a : Tagged W T B) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.includeResults_iter f a

/-- The successful fragment embeds faithfully, including its least iteration. -/
def resultsEmbedding : Embedding (Finite W) (Tagged W T) where
  map := includeResults
  injective := fun {_} {_ _} eq => Proofs.Semantics.NondeterministicTrace.Tagged.includeResults_injective eq
  map_pure := Proofs.Semantics.NondeterministicTrace.Tagged.includeResults_pure
  map_bind := Proofs.Semantics.NondeterministicTrace.Tagged.includeResults_bind
  map_iter := includeResults_iter

@[simp] theorem resultsEmbedding_map (p : Finite W A) :
    (resultsEmbedding (T := T)).map p = includeResults p := by rfl

variable [Monoid V] (h : W →* V)

theorem outcomes_mapLog (p : Tagged W T A) :
    (mapLog h p).outcomes = Prod.map id h '' p.outcomes := rfl

@[simp] theorem mapLog_pure (a : A) : mapLog h (pure a) = (pure a : Tagged V T A) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.mapLog_pure h a

theorem mapLog_bind (p : Tagged W T A) (k : A → Tagged W T B) :
    mapLog h (p >>= k) = mapLog h p >>= fun a => mapLog h (k a) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.mapLog_bind h p k

theorem mapLog_iter (f : A → Tagged W T (B ⊕ A)) (a : A) :
    mapLog h (iter f a) = iter (fun next => mapLog h (f next)) a :=
  Proofs.Semantics.NondeterministicTrace.Tagged.mapLog_iter h f a

theorem mapLog_injective (hh : Function.Injective h) :
    Function.Injective (mapLog h : Tagged W T A → Tagged V T A) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.mapLog_injective h hh

theorem mapLog_surjective (hh : Function.Surjective h) :
    Function.Surjective (mapLog h : Tagged W T A → Tagged V T A) :=
  Proofs.Semantics.NondeterministicTrace.Tagged.mapLog_surjective h hh

/-- An injective interpretation of logs embeds tagged computations. -/
def logEmbedding (hh : Function.Injective h) : Embedding (Tagged W T) (Tagged V T) where
  map := mapLog h
  injective := fun {_} {_ _} eq => mapLog_injective h hh eq
  map_pure := mapLog_pure h
  map_bind := mapLog_bind h
  map_iter := mapLog_iter h

@[simp] theorem logEmbedding_map (hh : Function.Injective h) (p : Tagged W T A) :
    (logEmbedding h hh).map p = mapLog h p := by rfl

/-- The surjective interpretation is the quotient by equal tagged log observations. -/
noncomputable def logQuotient (hh : Function.Surjective h) :
    Quotient (Setoid.ker (mapLog h : Tagged W T A → Tagged V T A)) ≃ Tagged V T A :=
  Setoid.quotientKerEquivOfSurjective (mapLog h) (mapLog_surjective h hh)

@[simp] theorem logQuotient_mk (hh : Function.Surjective h) (p : Tagged W T A) :
    logQuotient h hh (Quotient.mk _ p) = (mapLog h p : Tagged V T A) := by rfl

end Tagged
end Silmaril.Semantics.NondeterministicTrace
