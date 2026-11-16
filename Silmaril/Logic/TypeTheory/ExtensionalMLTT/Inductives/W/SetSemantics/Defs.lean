module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSemantics
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Operations
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetOps
public import Silmaril.Logic.SetTheory.Universes.Defs

@[expose] public section

/-! # Concrete set interpretation of object extensional MLTT with W-types

Every original term constructor has its original graph-model interpretation.
W types are the whole coded W carrier; constructor and recursor terms use the
proved actual set operations. This evaluator uses no chosen soundness algebra.
An infinite universe hierarchy is a supplied parameter, not constructed here;
`denoteIn` also supports finite universe supplies.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

noncomputable section

/-- Set interpretation from a level lookup, without assuming an infinite tower.

Closure and successor-membership laws are needed for soundness, not to interpret
syntax. This form therefore also interprets fragments using finite towers.
-/
def Tm.denoteIn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) :
    {k : ℕ} → (Fin k → ZFSet.{u}) → Tm k → ZFSet.{u}
  | _, _, .fv x => ρ x
  | _, β, .bv i => β i
  | _, _, .univ n => U n
  | _, _, .empty => ∅
  | _, _, .unit => SetSem.tt
  | _, _, .star => ∅
  | _, _, .nats => ZFSet.omega
  | _, _, .zero => ∅
  | _, β, .succ n => insert (denoteIn U ρ β n) (denoteIn U ρ β n)
  | _, β, .natrec _ s z n =>
      SetSem.natrec (denoteIn U ρ β z)
        (fun m acc => SetSem.app (denoteIn U ρ (Fin.cons m β) s) acc)
        (denoteIn U ρ β n)
  | _, β, .pi A B =>
      SetSem.pi (denoteIn U ρ β A) fun x => denoteIn U ρ (Fin.cons x β) B
  | _, β, .sigma A B =>
      SetSem.sigma (denoteIn U ρ β A) fun x => denoteIn U ρ (Fin.cons x β) B
  | _, β, .abs A b =>
      SetSem.lam (denoteIn U ρ β A) fun x => denoteIn U ρ (Fin.cons x β) b
  | _, β, .app f a => SetSem.app (denoteIn U ρ β f) (denoteIn U ρ β a)
  | _, β, .pair a b => SetSem.pair (denoteIn U ρ β a) (denoteIn U ρ β b)
  | _, β, .fst p => SetSem.fst (denoteIn U ρ β p)
  | _, β, .snd p => SetSem.snd (denoteIn U ρ β p)
  | _, β, .id _ a b => SetSem.truth (denoteIn U ρ β a = denoteIn U ρ β b)
  | _, _, .refl _ => ∅
  | _, _, .absurd _ _ => ∅
  | _, β, .wtype A B => WSet.carrier (denoteIn U ρ β A)
      (fun x => denoteIn U ρ (Fin.cons x β) B)
  | _, β, .sup A B a f => WSet.node (denoteIn U ρ β A)
      (fun x => denoteIn U ρ (Fin.cons x β) B)
      (denoteIn U ρ β a) (denoteIn U ρ β f)
  | _, β, .wrec A B _ s t => WSet.wrec (denoteIn U ρ β A)
      (fun x => denoteIn U ρ (Fin.cons x β) B)
      (denoteIn U ρ β s) (denoteIn U ρ β t)

/-- Interpretation of terms in a hierarchy and free/bound environments.

`absurd` has an arbitrary default on ill-typed arguments; valid empty-type
elimination has no semantic input. Identity proofs and the unit inhabitant
are represented by the empty set.
-/
def Tm.denote (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) :
    {k : ℕ} → (Fin k → ZFSet.{u}) → Tm k → ZFSet.{u}
  | _, _, .fv x => ρ x
  | _, β, .bv i => β i
  | _, _, .univ n => T.U n
  | _, _, .empty => ∅
  | _, _, .unit => SetSem.tt
  | _, _, .star => ∅
  | _, _, .nats => ZFSet.omega
  | _, _, .zero => ∅
  | _, β, .succ n => insert (denote T ρ β n) (denote T ρ β n)
  | _, β, .natrec _ s z n =>
      SetSem.natrec (denote T ρ β z)
        (fun m acc => SetSem.app (denote T ρ (Fin.cons m β) s) acc) (denote T ρ β n)
  | _, β, .pi A B => SetSem.pi (denote T ρ β A) fun x => denote T ρ (Fin.cons x β) B
  | _, β, .sigma A B => SetSem.sigma (denote T ρ β A) fun x => denote T ρ (Fin.cons x β) B
  | _, β, .abs A b => SetSem.lam (denote T ρ β A) fun x => denote T ρ (Fin.cons x β) b
  | _, β, .app f a => SetSem.app (denote T ρ β f) (denote T ρ β a)
  | _, β, .pair a b => SetSem.pair (denote T ρ β a) (denote T ρ β b)
  | _, β, .fst p => SetSem.fst (denote T ρ β p)
  | _, β, .snd p => SetSem.snd (denote T ρ β p)
  | _, β, .id _ a b => SetSem.truth (denote T ρ β a = denote T ρ β b)
  | _, _, .refl _ => ∅
  | _, _, .absurd _ _ => ∅
  | _, β, .wtype A B => WSet.carrier (denote T ρ β A)
      (fun x => denote T ρ (Fin.cons x β) B)
  | _, β, .sup A B a f => WSet.node (denote T ρ β A)
      (fun x => denote T ρ (Fin.cons x β) B)
      (denote T ρ β a) (denote T ρ β f)
  | _, β, .wrec A B _ s t => WSet.wrec (denote T ρ β A)
      (fun x => denote T ρ (Fin.cons x β) B)
      (denote T ρ β s) (denote T ρ β t)

/-- Every declared value belongs to the interpretation of its declared type. -/
def Ctx.Sat (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) : Ctx → Prop
  | .nil => True
  | .cons Γ x A => Γ.Sat T ρ ∧ ρ x ∈ A.denote T ρ Fin.elim0

/-- Names read by context satisfaction: declared names and names in declared types. -/
def Ctx.fvs : Ctx → Finset String
  | .nil => ∅
  | .cons Γ x A => insert x (Γ.fvs ∪ A.fvs)

/-- Equality and typing of a judgment in every environment satisfying its context. -/
def Jdg.Valid (T : SetHierarchy.{u}) (j : Jdg) : Prop :=
  ∀ ρ, j.Γ.Sat T ρ →
    j.a.denote T ρ Fin.elim0 = j.b.denote T ρ Fin.elim0 ∧
      j.a.denote T ρ Fin.elim0 ∈ j.A.denote T ρ Fin.elim0

/-- Context satisfaction using a possibly finite universe supply. -/
def Ctx.SatIn (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) : Ctx → Prop
  | .nil => True
  | .cons Γ x A => Γ.SatIn U ρ ∧ ρ x ∈ A.denoteIn U ρ Fin.elim0

/-- Judgment validity using a possibly finite universe supply. -/
def Jdg.ValidIn (U : ℕ → ZFSet.{u}) (j : Jdg) : Prop :=
  ∀ ρ, j.Γ.SatIn U ρ →
    j.a.denoteIn U ρ Fin.elim0 = j.b.denoteIn U ρ Fin.elim0 ∧
      j.a.denoteIn U ρ Fin.elim0 ∈ j.A.denoteIn U ρ Fin.elim0

end

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
