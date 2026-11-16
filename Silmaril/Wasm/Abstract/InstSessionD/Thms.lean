module

public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Wasm.Component.DWiring.Thms

/-!
# Core 3.0 instance sessions as a divergence-observing core semantics: theorems

**The read-back.** `spullD σ` has the finite plays `spull σ.toStrategy`
(`toStrategy_spullD`) and the preimages of the divergences and infinite plays of `σ`
(`mem_div_spullD`, `mem_inf_spullD`); it is monotone (`spullD_mono`). On an instance session its
finite plays are the instance strategy (`toStrategy_spullD_instSession`).

**Finite agreement.** Forgetting divergence and infinite plays gives back the existing core
semantics, by definition: `forget_threadSemSD : (threadSemSD T).forget = threadSemS T` and
`forget_core3SemD : (core3SemD P).forget = core3Sem P`. With the consistency of the
divergence-observing wiring (`Silmaril.Wasm.Component.DWiring.Thms`):

* `toStrategy_denUD_core3SemD : (c.denUD (core3SemD P)).toStrategy = c.denU (core3Sem P)`;
* `toStrategy_denD_core3SemD : (c.denD (core3SemD P)).toStrategy = c.den (core3Sem P)`;
* the same for flat components and programs, and for any session objects
  (`toStrategy_denUD_threadSemSD`).

So `Comp.denUD (core3SemD P)` refines `Comp.denU (core3Sem P)` exactly on finite plays, and adds
the divergences and infinite plays of components, computed by the `DivComp`/`DPair` laws
(`Silmaril.Wasm.Component.DWiringLaws`).

**Congruence, with divergence.** The session equalities of `InstSession` are equalities of
divergence-observing strategies, so they lift to the divergence-aware denotation, not only to its
finite plays: bisimilar store-retaining triples (`denUD_core3SemD_eq_of_obsEq`,
`denD_core3SemD_eq_of_obsEq`), triples agreeing on reachable stores
(`denUD_core3SemD_eq_of_reach`), and profiles with bisimilar triples
(`denUD_core3SemD_eq_of_obsEq_profile`) give the same `Comp.denUD`/`Comp.denD`.

Not claimed: adequacy against the reference component machine for general components (the next
step), the parser, F6.
-/

public section

namespace Silmaril.Wasm.Abstract.InstSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Reach ObsEq)
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-! ## The read-back -/

section Pull

variable {E : Sig.{0}} {ts : List FnType}

@[simp] theorem toStrategy_spullD (σ : DStrategy E (ssig ts)) :
    (spullD σ).toStrategy = spull σ.toStrategy := rfl

theorem mem_div_spullD {σ : DStrategy E (ssig ts)} {p : List (Move E (ifaceSig ts))} :
    p ∈ (spullD σ).div ↔ p.map srelabel ∈ σ.div := Iff.rfl

theorem mem_inf_spullD {σ : DStrategy E (ssig ts)} {J : Set (List (Move E (ifaceSig ts)))} :
    J ∈ (spullD σ).inf ↔ IsInfPlay J ∧ List.map srelabel '' J ∈ σ.inf := Iff.rfl

/-- The read-back is monotone. -/
theorem spullD_mono {σ τ : DStrategy E (ssig ts)} (h : σ ≤ τ) : spullD σ ≤ spullD τ :=
  ⟨Strategy.generate_mono fun _ hp => Strategy.le_def.1 h.1 hp, fun _ hp => h.2.1 hp,
    fun _ hJ => ⟨hJ.1, h.2.2 hJ.2⟩⟩

end Pull

/-- **The finite plays of an instance session, read back, are the instance strategy.** -/
theorem toStrategy_spullD_instSession (I : ScalarInstance) (P : Profile) (s : Store Nat) :
    (spullD (instSession I P s)).toStrategy = I.strategy P s :=
  spull_instSession s

/-! ## Finite agreement -/

@[simp] theorem toStrategy_semOfSD (m : NumInstance)
    (σ : DStrategy m.inst.E (ssig m.inst.exports)) :
    (semOfSD m σ).toStrategy = semOfS m σ := rfl

theorem forget_threadSemSD (T : (m : NumInstance) → DStrategy m.inst.E (ssig m.inst.exports)) :
    (threadSemSD T).forget = threadSemS T := rfl

/-- **The finite plays of the divergence-observing Core 3.0 semantics are `core3Sem P`.** -/
theorem forget_core3SemD (P : Profile) : (core3SemD P).forget = core3Sem P :=
  (core3Sem_eq_threadSemS P).symm

/-- Finite agreement for any session objects. -/
theorem toStrategy_denUD_threadSemSD
    (T : (m : NumInstance) → DStrategy m.inst.E (ssig m.inst.exports)) (c : Comp NumInstance) :
    (c.denUD (threadSemSD T)).toStrategy = c.denU (threadSemS T) :=
  toStrategy_denUD _ c

/-- **Finite agreement over `sigU`**: the divergence-aware denotation of a component over Core
3.0 instance sessions has exactly the finite plays of `Comp.denU (core3Sem P)`. -/
theorem toStrategy_denUD_core3SemD (P : Profile) (c : Comp NumInstance) :
    (c.denUD (core3SemD P)).toStrategy = c.denU (core3Sem P) := by
  rw [toStrategy_denUD, forget_core3SemD]

/-- **Finite agreement at the interface signatures.** -/
theorem toStrategy_denD_core3SemD (P : Profile) (c : Comp NumInstance) :
    (c.denD (core3SemD P)).toStrategy = c.den (core3Sem P) := by
  rw [toStrategy_denD, forget_core3SemD]

/-- Finite agreement for flat components. -/
theorem toStrategy_linked_denUD_core3SemD (P : Profile) (l : Linked NumInstance) :
    (l.denUD (core3SemD P)).toStrategy = l.denU (core3Sem P) := by
  rw [toStrategy_linked_denUD, forget_core3SemD]

/-- Finite agreement for programs. -/
theorem toStrategy_program_denUD_core3SemD (P : Profile) (p : Program NumInstance) :
    (p.denUD (core3SemD P)).toStrategy = p.denU (core3Sem P) := by
  rw [toStrategy_program_denUD, forget_core3SemD]

/-! ## Congruence, with divergence -/

/-- **Bisimilar store-retaining triples give the same divergence-aware denotation.** -/
theorem denUD_core3SemD_eq_of_obsEq {P : Profile} {S' : NumInstance → Type}
    (t : (m : NumInstance) → ObsTriple m.inst.E (S' m) m.inst.F.Op (Res m.inst.exports ⊕ PUnit))
    (s' : (m : NumInstance) → S' m)
    (h : ∀ m, ObsEq (instTripleS m.inst P) (t m) m.inst.store (s' m))
    (c : Comp NumInstance) :
    c.denUD (core3SemD P) = c.denUD (threadSemSD fun m => threadS (t m) (s' m)) :=
  congrArg (fun T => c.denUD (threadSemSD T))
    (funext fun m => StratSession.threadS_eq_of_obsEq (h m))

/-- Bisimilar triples give the same divergence-aware denotation at the interface signatures. -/
theorem denD_core3SemD_eq_of_obsEq {P : Profile} {S' : NumInstance → Type}
    (t : (m : NumInstance) → ObsTriple m.inst.E (S' m) m.inst.F.Op (Res m.inst.exports ⊕ PUnit))
    (s' : (m : NumInstance) → S' m)
    (h : ∀ m, ObsEq (instTripleS m.inst P) (t m) m.inst.store (s' m))
    (c : Comp NumInstance) :
    c.denD (core3SemD P) = c.denD (threadSemSD fun m => threadS (t m) (s' m)) :=
  congrArg (DStrategy.atSizes _ _) (denUD_core3SemD_eq_of_obsEq t s' h c)

/-- **Triples agreeing on reachable stores give the same divergence-aware denotation.** -/
theorem denUD_core3SemD_eq_of_reach {P : Profile}
    (t : (m : NumInstance) →
      ObsTriple m.inst.E (Store Nat) m.inst.F.Op (Res m.inst.exports ⊕ PUnit))
    (h : ∀ m s, m.inst.ReachableStore P m.inst.store s →
      (instTripleS m.inst P).1 s = (t m).1 s ∧ satP (instTripleS m.inst P) s = satP (t m) s ∧
        (instTripleS m.inst P).2.2 s = (t m).2.2 s)
    (c : Comp NumInstance) :
    c.denUD (core3SemD P) = c.denUD (threadSemSD fun m => threadS (t m) m.inst.store) :=
  congrArg (fun T => c.denUD (threadSemSD T)) (funext fun m =>
    StratSession.threadS_congr fun s hs => h m s (reach_iff_reachableStore.1 hs))

/-- Two profiles whose store-retaining instance triples are bisimilar at the instantiation stores
give the same divergence-aware denotation. -/
theorem denUD_core3SemD_eq_of_obsEq_profile {P Q : Profile}
    (h : ∀ m : NumInstance,
      ObsEq (instTripleS m.inst P) (instTripleS m.inst Q) m.inst.store m.inst.store)
    (c : Comp NumInstance) : c.denUD (core3SemD P) = c.denUD (core3SemD Q) :=
  denUD_core3SemD_eq_of_obsEq _ _ h c

end Silmaril.Wasm.Abstract.InstSession
