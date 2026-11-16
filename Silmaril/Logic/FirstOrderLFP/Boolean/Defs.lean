module

public import Silmaril.Logic.FirstOrderLFP.Thms

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Boolean
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- A polarity records syntactic variance in each free recursive predicate.
The object-variable context and arbitrary finite predicate profiles are retained. -/
inductive Formula (S : Signature) : {r k : Nat} →
    (Fin r → Profile S) → (Fin k → S.S) → (Fin r → Bool) → Type where
  | base {r k P Γ σ} : FOL.Formula S Γ → Formula (r := r) (k := k) S P Γ σ
  | pred {r k P Γ σ} (i : Fin r) (positive : σ i = true)
      (args : ∀ j, EQ.Term S.toSignature Γ ((P i).sorts j)) : Formula (k := k) S P Γ σ
  | neg {r k P Γ σ} : Formula (r := r) (k := k) S P Γ (fun i => !(σ i)) → Formula S P Γ σ
  | conj {r k P Γ σ} : Formula (r := r) (k := k) S P Γ σ → Formula S P Γ σ → Formula S P Γ σ
  | disj {r k P Γ σ} : Formula (r := r) (k := k) S P Γ σ → Formula S P Γ σ → Formula S P Γ σ
  | all {r k P σ} {Δ : Fin (k + 1) → S.S} :
      Formula (r := r) S P Δ σ → Formula S P (Δ ∘ Fin.succ) σ
  | ex {r k P σ} {Δ : Fin (k + 1) → S.S} :
      Formula (r := r) S P Δ σ → Formula S P (Δ ∘ Fin.succ) σ
  | lfp {r k} {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
      {σ : Fin r → Bool} {Δ : Fin ((P' 0).arity + k) → S.S}
      (tupleSorts : Δ ∘ Fin.castAdd k = (P' 0).sorts)
      (parameterSorts : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
      (body : Formula S P' Δ (Fin.cases true σ))
      (args : ∀ j, EQ.Term S.toSignature Γ ((P' 0).sorts j)) :
      Formula S (P' ∘ Fin.succ) Γ σ

/-- Inclusion is reversed at negative predicate entries. -/
def RelLE {S : Signature} {M : Model S} {r : Nat} {P : Fin r → Profile S}
    (σ : Fin r → Bool) (η ζ : RelEnv M P) : Prop :=
  ∀ i, if σ i then η i ⊆ ζ i else ζ i ⊆ η i

theorem RelLE.flip {S : Signature} {M : Model S} {r : Nat} {P : Fin r → Profile S}
    {σ : Fin r → Bool} {η ζ : RelEnv M P} (h : RelLE σ η ζ) :
    RelLE (fun i => !(σ i)) ζ η := by
  intro i
  have hi := h i
  cases hs : σ i <;> simpa [hs] using hi

/-- A directly interpreted formula, monotone for its declared mixed variance. -/
structure Meaning {S : Signature} (M : Model S) {r k : Nat}
    (P : Fin r → Profile S) (Γ : Fin k → S.S) (σ : Fin r → Bool) where
  run : RelEnv M P → Set (ObjEnv M Γ)
  monotone : ∀ {η ζ}, RelLE σ η ζ → run η ⊆ run ζ

instance {S : Signature} {M : Model S} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} {σ : Fin r → Bool} : CoeFun (Meaning M P Γ σ)
      (fun _ => RelEnv M P → Set (ObjEnv M Γ)) := ⟨Meaning.run⟩

@[ext] theorem Meaning.ext {S : Signature} {M : Model S} {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    (p q : Meaning M P Γ σ) (h : p.run = q.run) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Independent Boolean FO(LFP) semantics: negation is set complement and the
fresh positive recursive predicate is interpreted by a genuine least fixed point.
No matching/modal translation, finite unfolding or finite carrier is involved. -/
noncomputable def Formula.denote {S : Signature} (M : Model S) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    (p : Formula S P Γ σ) : Meaning M P Γ σ := by
  induction p with
  | base p => exact ⟨fun _ => {ρ | p.Holds M.toStructure ρ}, by intro η ζ h; exact le_rfl⟩
  | pred i positive args =>
      exact ⟨fun η => {ρ | (fun j => (args j).eval M.toStructure.toAlgebra ρ) ∈ η i}, by
        intro η ζ h ρ hρ
        exact (show η i ⊆ ζ i by simpa [positive] using h i) hρ⟩
  | neg p dp =>
      exact ⟨fun η => (dp η)ᶜ, by
        intro η ζ h ρ hρ hζ
        exact hρ (dp.monotone h.flip hζ)⟩
  | conj p q dp dq =>
      exact ⟨fun η => dp η ∩ dq η, by
        intro η ζ h ρ hv
        exact ⟨dp.monotone h hv.1, dq.monotone h hv.2⟩⟩
  | disj p q dp dq =>
      exact ⟨fun η => dp η ∪ dq η, by
        intro η ζ h ρ hv
        exact hv.elim (fun hp => Or.inl (dp.monotone h hp)) (fun hq => Or.inr (dq.monotone h hq))⟩
  | @all r k P σ Δ p dp =>
      exact ⟨fun η => {ρ | ∀ x : M.toStructure.carrier (Δ 0), Fin.cases x ρ ∈ dp η},
        by intro η ζ h ρ hv x; exact dp.monotone h (hv x)⟩
  | @ex r k P σ Δ p dp =>
      exact ⟨fun η => {ρ | ∃ x : M.toStructure.carrier (Δ 0), Fin.cases x ρ ∈ dp η},
        by
        intro η ζ h ρ hv
        obtain ⟨x, hx⟩ := hv
        exact ⟨x, dp.monotone h hx⟩⟩
  | @lfp r k P' Γ σ Δ ht hp p args dp =>
      let F (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
          Set (Tuple M (P' 0)) →o Set (Tuple M (P' 0)) :=
        ⟨fun X => {x | ∀ θ : ObjEnv M Δ, Extends θ x ρ → θ ∈ dp (insertRel M P' η X)}, by
          intro X Y h x hx θ hθ
          apply dp.monotone ?_ (hx θ hθ)
          intro i
          refine Fin.cases h (fun j => ?_) i
          change if σ j then η j ⊆ η j else η j ⊆ η j
          split <;> exact le_rfl⟩
      exact ⟨fun η => {ρ | (fun j => (args j).eval M.toStructure.toAlgebra ρ) ∈ (F η ρ).lfp}, by
        intro η ζ h ρ hρ
        have hF : F η ρ ≤ F ζ ρ := by
          intro X x hx θ hθ
          apply dp.monotone ?_ (hx θ hθ)
          intro i
          exact Fin.cases le_rfl (fun j => h j) i
        exact (show (F η ρ).lfp ⊆ (F ζ ρ).lfp from OrderHom.lfp.monotone hF) hρ⟩

def Formula.map {S T : Signature} (f : S ⟶ T) : {r k : Nat} →
    {P : Fin r → Profile S} → {Γ : Fin k → S.S} → {σ : Fin r → Bool} →
    Formula S P Γ σ → Formula T (fun i => (P i).map f) (f.sorts ∘ Γ) σ
  | _, _, _, _, _, .base p => .base (p.map f)
  | _, _, _, _, _, .pred i positive args => .pred i positive (fun j => (args j).map f.toHom)
  | _, _, _, _, _, .neg p => .neg (p.map f)
  | _, _, _, _, _, .conj p q => .conj (p.map f) (q.map f)
  | _, _, _, _, _, .disj p q => .disj (p.map f) (q.map f)
  | _, _, _, _, _, .all p => .all (p.map f)
  | _, _, _, _, _, .ex p => .ex (p.map f)
  | _, _, _, _, _, .lfp ht hp p args => .lfp
      (congrArg (f.sorts ∘ ·) ht) (congrArg (f.sorts ∘ ·) hp) (p.map f)
      (fun j => (args j).map f.toHom)

/-- The original positive grammar may use any context whose entries are positive. -/
def positiveWith {S : Signature} : {r k : Nat} → {P : Fin r → Profile S} →
    {Γ : Fin k → S.S} → (p : FirstOrderLFP.Formula S P Γ) →
    (σ : Fin r → Bool) → (∀ i, σ i = true) → Formula S P Γ σ
  | _, _, _, _, .base p, _, _ => .base p
  | _, _, _, _, .pred i args, _, hσ => .pred i (hσ i) args
  | _, _, _, _, .conj p q, σ, hσ => .conj (positiveWith p σ hσ) (positiveWith q σ hσ)
  | _, _, _, _, .disj p q, σ, hσ => .disj (positiveWith p σ hσ) (positiveWith q σ hσ)
  | _, _, _, _, .all p, σ, hσ => .all (positiveWith p σ hσ)
  | _, _, _, _, .ex p, σ, hσ => .ex (positiveWith p σ hσ)
  | _, _, _, _, .lfp ht hpar p args, σ, hσ =>
      .lfp ht hpar (positiveWith p (Fin.cases true σ) (fun i => Fin.cases rfl hσ i)) args

/-- The original positive syntax embeds without altering terms or binders. -/
def positive {S : Signature} {r k : Nat} {P : Fin r → Profile S} {Γ : Fin k → S.S}
    (p : FirstOrderLFP.Formula S P Γ) : Formula S P Γ (fun _ => true) :=
  positiveWith p (fun _ => true) (fun _ => rfl)

end Silmaril.Logic.FirstOrderLFP.Boolean
