module

public import Silmaril.Logic.Matching.FirstOrder.Pointed
public import Mathlib.Order.FixedPoints
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {S : Type} (A : Signature S)

/-- Positive normal form: every free set variable occurs positively.
The 2017 syntax is retained verbatim as recursion-independent leaves. -/
inductive Pattern : {r k : Nat} → (Fin r → S) → (Fin k → S) → S → Type where
  | base {r k P Γ s} : FirstOrder.Pattern (k := k) A Γ s → Pattern (r := r) P Γ s
  | setvar {r k P Γ} (i : Fin r) : Pattern (k := k) P Γ (P i)
  | app {r k P Γ n inputs output} (op : A.operations n inputs output)
      (args : ∀ i, Pattern (r := r) (k := k) P Γ (inputs i)) : Pattern P Γ output
  | dualApp {r k P Γ n inputs output} (op : A.operations n inputs output)
      (args : ∀ i, Pattern (r := r) (k := k) P Γ (inputs i)) : Pattern P Γ output
  | conj {r k P Γ s} : Pattern (r := r) (k := k) P Γ s → Pattern P Γ s → Pattern P Γ s
  | disj {r k P Γ s} : Pattern (r := r) (k := k) P Γ s → Pattern P Γ s → Pattern P Γ s
  | ex {r k P Γ s} (bound : S) (body : Pattern (r := r) (k := k+1) P (Fin.cases bound Γ) s) :
      Pattern (k := k) P Γ s
  | all {r k P Γ s} (bound : S) (body : Pattern (r := r) (k := k+1) P (Fin.cases bound Γ) s) :
      Pattern (k := k) P Γ s
  | mu {r k} {P' : Fin (r+1) → S} {Γ : Fin k → S}
      (body : Pattern P' Γ (P' 0)) : Pattern (P' ∘ Fin.succ) Γ (P' 0)
  | nu {r k} {P' : Fin (r+1) → S} {Γ : Fin k → S}
      (body : Pattern P' Γ (P' 0)) : Pattern (P' ∘ Fin.succ) Γ (P' 0)

abbrev Model (A : Signature S) := FirstOrder.Model A
abbrev ObjEnv (M : Model A) {k : Nat} (Γ : Fin k → S) := ∀ i, M.carrier (Γ i)
abbrev SetEnv (M : Model A) {r : Nat} (P : Fin r → S) := ∀ i, Set (M.carrier (P i))

def insert (A : Signature S) (M : Model A) {r : Nat} {P' : Fin (r+1) → S}
    (η : SetEnv A M (P' ∘ Fin.succ)) : Set (M.carrier (P' 0)) →o SetEnv A M P' where
  toFun X := Fin.cases X η
  monotone' := fun _ _ h i => Fin.cases h (fun _ => le_rfl) i

/-- Exactly the existential set extension of the existing 2017 operation. -/
def application {A : Signature S} (M : Model A) {n inputs output}
    (op : A.operations n inputs output) (args : ∀ i, Set (M.carrier (inputs i))) :
    Set (M.carrier output) :=
  {result | ∃ values, (∀ i, values i ∈ args i) ∧ result ∈ M.operation op values}

/-- On old patterns this is definitionally the original 2017 application semantics. -/
theorem application_firstOrder {A : Signature S} (M : Model A) {k n : Nat}
    {Γ : Fin k → S} {inputs : Fin n → S} {output : S}
    (v : ObjEnv A M Γ) (op : A.operations n inputs output)
    (args : ∀ i, FirstOrder.Pattern A Γ (inputs i)) :
    application M op (fun i => M.denote v (args i)) = M.denote v (.app op args) := rfl

/-- Derived De Morgan application: complement the old application of complements. -/
def dualApplication {A : Signature S} (M : Model A) {n inputs output}
    (op : A.operations n inputs output) (args : ∀ i, Set (M.carrier (inputs i))) :
    Set (M.carrier output) := (application M op (fun i => (args i)ᶜ))ᶜ

theorem application_mono {A : Signature S} (M : Model A) {n inputs output}
    (op : A.operations n inputs output) {a b : ∀ i, Set (M.carrier (inputs i))} (h : a ≤ b) :
    application M op a ⊆ application M op b :=
  fun _ ⟨v, hv, ho⟩ => ⟨v, fun i => h i (hv i), ho⟩

theorem dualApplication_mono {A : Signature S} (M : Model A) {n inputs output}
    (op : A.operations n inputs output) {a b : ∀ i, Set (M.carrier (inputs i))} (h : a ≤ b) :
    dualApplication M op a ⊆ dualApplication M op b := by
  intro result ha hb
  exact ha (application_mono M op (fun i => Set.compl_subset_compl.mpr (h i)) hb)

/-- Genuine set least/greatest fixed points; the captured object valuation is fixed. -/
noncomputable def Pattern.denote {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s)
    (v : ObjEnv A M Γ) : SetEnv A M P →o Set (M.carrier s) := by
  induction p with
  | base p => exact ⟨fun _ => M.denote v p, fun _ _ _ => le_rfl⟩
  | setvar i => exact ⟨fun η => η i, fun _ _ h => h i⟩
  | app op args ih =>
      exact ⟨fun η => application M op (fun i => ih i v η),
        fun _ _ h => application_mono M op (fun i => (ih i v).monotone h)⟩
  | dualApp op args ih =>
      exact ⟨fun η => dualApplication M op (fun i => ih i v η),
        fun _ _ h => dualApplication_mono M op (fun i => (ih i v).monotone h)⟩
  | conj p q dp dq => exact ⟨fun η => dp v η ∩ dq v η,
      fun _ _ h _ hx => ⟨(dp v).monotone h hx.1, (dq v).monotone h hx.2⟩⟩
  | disj p q dp dq => exact ⟨fun η => dp v η ∪ dq v η,
      fun _ _ h _ hx => hx.elim (fun hp => Or.inl ((dp v).monotone h hp))
        (fun hq => Or.inr ((dq v).monotone h hq))⟩
  | ex bound body dp => exact ⟨fun η => {x | ∃ a : M.carrier bound, x ∈ dp (Fin.cases a v) η},
      fun _ _ h _ ⟨a, ha⟩ => ⟨a, (dp _).monotone h ha⟩⟩
  | all bound body dp => exact ⟨fun η => {x | ∀ a : M.carrier bound, x ∈ dp (Fin.cases a v) η},
      fun _ _ h _ ha a => (dp _).monotone h (ha a)⟩
  | mu body dp => exact ⟨fun η => ((dp v).comp (insert A M η)).lfp, by
      intro η ζ h
      apply OrderHom.lfp.monotone
      intro X
      exact (dp v).monotone (fun i => Fin.cases le_rfl (fun j => h j) i)⟩
  | nu body dp => exact ⟨fun η => ((dp v).comp (insert A M η)).gfp, by
      intro η ζ h
      apply OrderHom.gfp.monotone
      intro X
      exact (dp v).monotone (fun i => Fin.cases le_rfl (fun j => h j) i)⟩

def Pattern.map {A B : Signature S} (f : A ⟶ B) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) : Pattern B P Γ s := by
  induction p with
  | base p => exact .base (FirstOrder.Pattern.map f p)
  | setvar i => exact .setvar i
  | app op args ih => exact .app (f.operations op) ih
  | dualApp op args ih => exact .dualApp (f.operations op) ih
  | conj p q hp hq => exact .conj hp hq
  | disj p q hp hq => exact .disj hp hq
  | ex bound p hp => exact .ex bound hp
  | all bound p hp => exact .all bound hp
  | mu p hp => exact .mu hp
  | nu p hp => exact .nu hp

end Silmaril.Logic.Matching.FixedPoint
