module

public import Silmaril.Semantics.Calco2019.Examples.SetModels.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.SetModels

/-! # Truncation and nonempty powersets in CALCO 2019 Examples 10 and 20 -/

public section

universe u

namespace Silmaril.Calco2019.Examples.SetModels

theorem trunc_nonempty_iff (X : Type u) : Nonempty (Trunc X) ↔ Nonempty X :=
  Proofs.trunc_nonempty_iff X

theorem trunc_guarded_each :
    truncGuard.guarded (computation Trunc truncChoice) ∧
      truncGuard.left (computation Trunc truncChoice) :=
  Proofs.trunc_guarded_each

theorem trunc_union_unguarded :
    ¬ truncGuard.guarded (computation Trunc
      (fun x : Unit => Trunc.map Sum.inr (truncChoice x) : Unit → Trunc (Empty ⊕ (Unit ⊕ Unit)))) :=
  Proofs.trunc_union_unguarded

/-- Example 20(1). The truncation guard is the least guard from Proposition 9. -/
theorem trunc_iterative : IsGuardedIterative typeCoproducts truncGuard.{u} :=
  Guardedness.vacuous_iterative

theorem powerset_isElgot : (powersetElgot.{u}).IsElgot :=
  ofLawfulMonad_isElgot SetM

/-- Example 20(2). The nondeterministic solution is least among sets closed under unfolding. -/
theorem powerset_least {X Y : Type u} (f : X → SetM (Y ⊕ X)) (g : X → SetM Y)
    (hg : ∀ x, (f x >>= Sum.elim pure g).run ⊆ (g x).run) (x : X) :
    (Elgot.iter f x).run ⊆ (g x).run :=
  Proofs.powerset_least f g hg x

theorem powerset_iter_nonempty {X Y : Type u} (f : X → SetM (Y ⊕ X))
    (hf : HasDirectReturn f) (x : X) : (Elgot.iter f x).run.Nonempty :=
  Proofs.powerset_iter_nonempty f hf x

/-- The successful finite-run solution of the paper as a nonempty powerset. -/
noncomputable def nonemptyIter {X Y : Type u} (f : X → NonemptyPowerset (Y ⊕ X))
    (hf : HasDirectReturn fun x => (f x).1) (x : X) : NonemptyPowerset Y :=
  ⟨Elgot.iter (fun x => (f x).1) x, powerset_iter_nonempty _ hf x⟩

@[simp] theorem nonemptyIter_val {X Y : Type u} (f : X → NonemptyPowerset (Y ⊕ X))
    (hf : HasDirectReturn fun x => (f x).1) (x : X) :
    (nonemptyIter f hf x).1 = Elgot.iter (fun a => (f a).1) x := by
  unfold nonemptyIter
  rfl

theorem mem_nonemptyIter {X Y : Type u} (f : X → NonemptyPowerset (Y ⊕ X))
    (hf : HasDirectReturn fun x => (f x).1) (x : X) (y : Y) :
    y ∈ (nonemptyIter f hf x).1.run ↔ Elgot.Nondet.Runs (fun x => (f x).1) x y :=
  Elgot.Nondet.mem_iter_iff _ x y

end Silmaril.Calco2019.Examples.SetModels
