module

public import Silmaril.Logic.Institution.Examples.FirstOrder
public import Silmaril.Logic.Institution.Borrowing
public import Mathlib.Order.FixedPoints

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP
open CategoryTheory Silmaril.Logic.Institution.Examples

abbrev Signature := FOL.Signature

structure Profile (S : Signature) where
  arity : Nat
  sorts : Fin arity → S.S

def Profile.map {S T : Signature} (f : S ⟶ T) (p : Profile S) : Profile T :=
  ⟨p.arity, f.sorts ∘ p.sorts⟩

/-- Positive recursive predicates, with independently scoped sorted object variables.
Base FOL formulas may contain arbitrary negations, but no recursive predicate.
LFP bodies bind a tuple prefix and retain all ambient object parameters. -/
inductive Formula (S : Signature) : {r k : Nat} →
    (Fin r → Profile S) → (Fin k → S.S) → Type where
  | base {r k} {P : Fin r → Profile S} {Γ : Fin k → S.S} : FOL.Formula S Γ → Formula S P Γ
  | pred {r k} {P : Fin r → Profile S} {Γ : Fin k → S.S} (i : Fin r)
      (args : ∀ j, EQ.Term S.toSignature Γ ((P i).sorts j)) : Formula S P Γ
  | conj {r k} {P : Fin r → Profile S} {Γ : Fin k → S.S} :
      Formula S P Γ → Formula S P Γ → Formula S P Γ
  | disj {r k} {P : Fin r → Profile S} {Γ : Fin k → S.S} :
      Formula S P Γ → Formula S P Γ → Formula S P Γ
  | all {r k} {P : Fin r → Profile S} {Δ : Fin (k + 1) → S.S} :
      Formula S P Δ → Formula S P (Δ ∘ Fin.succ)
  | ex {r k} {P : Fin r → Profile S} {Δ : Fin (k + 1) → S.S} :
      Formula S P Δ → Formula S P (Δ ∘ Fin.succ)
  | lfp {r k} {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
      {Δ : Fin ((P' 0).arity + k) → S.S}
      (tupleSorts : Δ ∘ Fin.castAdd k = (P' 0).sorts)
      (parameterSorts : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
      (body : Formula S P' Δ)
      (args : ∀ j, EQ.Term S.toSignature Γ ((P' 0).sorts j)) :
      Formula S (P' ∘ Fin.succ) Γ

def Formula.map {S T : Signature} (f : S ⟶ T) : {r k : Nat} →
    {P : Fin r → Profile S} → {Γ : Fin k → S.S} →
    Formula S P Γ → Formula T (fun i => (P i).map f) (f.sorts ∘ Γ)
  | _, _, _, _, .base p => .base (p.map f)
  | _, _, _, _, .pred i args => .pred i (fun j => (args j).map f.toHom)
  | _, _, _, _, .conj p q => .conj (p.map f) (q.map f)
  | _, _, _, _, .disj p q => .disj (p.map f) (q.map f)
  | _, _, _, _, .all p => .all (p.map f)
  | _, _, _, _, .ex p => .ex (p.map f)
  | _, _, _, _, .lfp ht hp p args => .lfp
      (congrArg (f.sorts ∘ ·) ht) (congrArg (f.sorts ∘ ·) hp) (p.map f)
      (fun j => (args j).map f.toHom)

/-- The public FOL structures, including empty carriers, with equality-only arrows. -/
structure Model (S : Signature) : Type 1 where
  toStructure : FOL.Structure S

instance (S : Signature) : Category (Model S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

abbrev ObjEnv {S : Signature} (M : Model S) {k : Nat} (Γ : Fin k → S.S) :=
  ∀ i, M.toStructure.carrier (Γ i)

abbrev Tuple {S : Signature} (M : Model S) (p : Profile S) := ObjEnv M p.sorts

abbrev RelEnv {S : Signature} (M : Model S) {r : Nat} (P : Fin r → Profile S) :=
  ∀ i, Set (Tuple M (P i))

/-- The fresh recursive relation is index zero; all outer predicates retain their profiles. -/
def insertRel {S : Signature} (M : Model S) {r : Nat} (P' : Fin (r + 1) → Profile S)
    (η : RelEnv M (P' ∘ Fin.succ)) : Set (Tuple M (P' 0)) →o RelEnv M P' where
  toFun X := Fin.cases X η
  monotone' := by
    intro X Y h i
    exact Fin.cases h (fun _ => le_rfl) i

/-- Agreement of a body valuation with its bound tuple and captured parameters. -/
def Extends {S : Signature} {M : Model S} {n k : Nat}
    {Δ : Fin (n + k) → S.S} {w : Fin n → S.S} {Γ : Fin k → S.S}
    (θ : ObjEnv M Δ) (x : ObjEnv M w) (ρ : ObjEnv M Γ) : Prop :=
  (∀ j, HEq (θ (Fin.castAdd k j)) (x j)) ∧
    (∀ i, HEq (θ (Fin.natAdd n i)) (ρ i))

/-- Every formula denotes a monotone map of all free recursive predicates. -/
noncomputable def Formula.denote {S : Signature} (M : Model S) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : Formula S P Γ) :
    RelEnv M P →o Set (ObjEnv M Γ) := by
  induction p with
  | base p => exact ⟨fun _ => {ρ | p.Holds M.toStructure ρ}, fun _ _ _ => le_rfl⟩
  | pred i args =>
      exact ⟨fun η => {ρ | (fun j => (args j).eval M.toStructure.toAlgebra ρ) ∈ η i},
        fun _ _ h => fun _ hv => h i hv⟩
  | conj p q dp dq =>
      exact ⟨fun η => dp η ∩ dq η,
        fun _ _ h => fun _ hv => ⟨dp.monotone h hv.1, dq.monotone h hv.2⟩⟩
  | disj p q dp dq =>
      exact ⟨fun η => dp η ∪ dq η,
        fun _ _ h => fun _ hv => hv.elim
          (fun hp => Or.inl (dp.monotone h hp)) (fun hq => Or.inr (dq.monotone h hq))⟩
  | @all r k P Δ p dp =>
      exact ⟨fun η => {ρ | ∀ x : M.toStructure.carrier (Δ 0), Fin.cases x ρ ∈ dp η},
        fun _ _ h => fun _ hv x => dp.monotone h (hv x)⟩
  | @ex r k P Δ p dp =>
      exact ⟨fun η => {ρ | ∃ x : M.toStructure.carrier (Δ 0), Fin.cases x ρ ∈ dp η},
        fun _ _ h => fun _ ⟨x, hx⟩ => ⟨x, dp.monotone h hx⟩⟩
  | @lfp r k P' Γ Δ ht hp p args dp =>
      let F (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
          Set (Tuple M (P' 0)) →o Set (Tuple M (P' 0)) :=
        ⟨fun X => {x | ∀ θ : ObjEnv M Δ, Extends θ x ρ → θ ∈ dp (insertRel M P' η X)},
          fun _ _ h => fun _ hx θ hθ => dp.monotone ((insertRel M P' η).monotone h) (hx θ hθ)⟩
      exact ⟨fun η => {ρ | (fun j => (args j).eval M.toStructure.toAlgebra ρ) ∈ (F η ρ).lfp}, by
        intro η ζ h ρ hρ
        have hF : F η ρ ≤ F ζ ρ := by
          intro X x hx θ hθ
          apply dp.monotone ?_ (hx θ hθ)
          intro i
          exact Fin.cases le_rfl (fun j => h j) i
        exact (show (F η ρ).lfp ⊆ (F ζ ρ).lfp from OrderHom.lfp.monotone hF) hρ⟩

/-- Both recursive and object-variable contexts are empty in sentences. -/
structure Sentence (S : Signature) where
  profiles : Fin 0 → Profile S
  context : Fin 0 → S.S
  formula : Formula S profiles context

def Sentence.map {S T : Signature} (f : S ⟶ T) (p : Sentence S) : Sentence T :=
  ⟨fun i => (p.profiles i).map f, f.sorts ∘ p.context, p.formula.map f⟩

def Sat {S : Signature} (M : Model S) (p : Sentence S) : Prop :=
  (fun i => i.elim0) ∈ p.formula.denote M (fun i => i.elim0)

/-- The reduct is the actual public FOL structure reduct. -/
def reduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj M := ⟨(FOL.Structure.reduct f).obj M.toStructure⟩
  map h := ⟨congrArg (fun M => Model.mk ((FOL.Structure.reduct f).obj M.toStructure)) h.down⟩

end Silmaril.Logic.FirstOrderLFP
