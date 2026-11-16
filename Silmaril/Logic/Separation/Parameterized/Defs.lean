module

public import Silmaril.Logic.Separation.Thms
public import Silmaril.Logic.FirstOrderLFP.Thms

/-! Parameterized positive recursive separation over one arbitrary value sort.
A recursive predicate receives both an argument tuple and an actual resource.
Object binders range over values; spatial connectives split only resources. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized
open CategoryTheory Silmaril.Logic.Institution

structure Signature where
  Op : Nat → Type
  Atom : Nat → Type

structure Model (A : Signature) where
  Value : Type
  resource : Separation.Resource
  operation : ∀ {n}, A.Op n → (Fin n → Value) → Value
  atom : ∀ {n}, A.Atom n → (Fin n → Value) → Set resource.carrier

inductive Term (A : Signature) (k : Nat) where
  | var : Fin k → Term A k
  | app {n} : A.Op n → (Fin n → Term A k) → Term A k

def Term.eval {A : Signature} (M : Model A) {k} (ρ : Fin k → M.Value) :
    Term A k → M.Value
  | .var i => ρ i
  | .app op args => M.operation op (fun i => (args i).eval M ρ)

/-- No recursive predicates occur in an assertion used under arbitrary negation
or in a wand antecedent. Pure equality does not consume resource ownership. -/
inductive Assertion (A : Signature) (k : Nat) where
  | eq : Term A k → Term A k → Assertion A k
  | atom {n} : A.Atom n → (Fin n → Term A k) → Assertion A k
  | emp : Assertion A k
  | neg : Assertion A k → Assertion A k
  | conj : Assertion A k → Assertion A k → Assertion A k
  | sep : Assertion A k → Assertion A k → Assertion A k
  | wand : Assertion A k → Assertion A k → Assertion A k

def Assertion.denote {A : Signature} (M : Model A) {k} (ρ : Fin k → M.Value) :
    Assertion A k → Set M.resource.carrier
  | .eq t u => {_h | t.eval M ρ = u.eval M ρ}
  | .atom a args => M.atom a (fun i => (args i).eval M ρ)
  | .emp => {M.resource.unit}
  | .neg p => (p.denote M ρ)ᶜ
  | .conj p q => p.denote M ρ ∩ q.denote M ρ
  | .sep p q => M.resource.sep (p.denote M ρ) (q.denote M ρ)
  | .wand p q => M.resource.wand (p.denote M ρ) (q.denote M ρ)

/-- A profile is the finite number of value arguments; a resource argument is
always present separately. The LFP body binds a fresh value tuple prefix and
retains every ambient value parameter. -/
inductive Pattern (A : Signature) : {r : Nat} → (Fin r → Nat) → Nat → Type where
  | base {r P k} : Assertion A k → Pattern (r := r) A P k
  | pred {r P k} (i : Fin r) : (Fin (P i) → Term A k) → Pattern A P k
  | conj {r P k} : Pattern (r := r) A P k → Pattern A P k → Pattern A P k
  | disj {r P k} : Pattern (r := r) A P k → Pattern A P k → Pattern A P k
  | sep {r P k} : Pattern (r := r) A P k → Pattern A P k → Pattern A P k
  | wand {r P k} : Assertion A k → Pattern (r := r) A P k → Pattern A P k
  | ex {r P k} : Pattern (r := r) A P (k+1) → Pattern A P k
  | all {r P k} : Pattern (r := r) A P (k+1) → Pattern A P k
  | lfp {r k} {P' : Fin (r+1) → Nat} :
      Pattern A P' (P' 0 + k) → (Fin (P' 0) → Term A k) → Pattern A (P' ∘ Fin.succ) k

abbrev Tuple {A : Signature} (M : Model A) (n : Nat) := Fin n → M.Value
def consValues {A : Signature} (M : Model A) {k} (x : M.Value) (ρ : Tuple M k) : Tuple M (k+1) :=
  Fin.cases x ρ

def appendValues {A : Signature} (M : Model A) {n k} (x : Tuple M n) (ρ : Tuple M k) : Tuple M (n+k) :=
  Fin.addCases x ρ

abbrev State {A : Signature} (M : Model A) (k : Nat) := Tuple M k × M.resource.carrier
abbrev RelEnv {A : Signature} (M : Model A) {r} (P : Fin r → Nat) :=
  ∀ i, Set (State M (P i))

def insert {A : Signature} (M : Model A) {r} (P' : Fin (r+1) → Nat)
    (η : RelEnv M (P' ∘ Fin.succ)) : Set (State M (P' 0)) →o RelEnv M P' where
  toFun X := Fin.cases X η
  monotone' := fun _ _ h i => Fin.cases h (fun _ => le_rfl) i

/-- Direct full-powerset resource semantics. Neither a compiler nor a bounded
heap/fuel interpretation occurs in this definition. -/
def Pattern.denote {A : Signature} (M : Model A) {r k} {P : Fin r → Nat}
    (p : Pattern A P k) : RelEnv M P →o Set (State M k) := by
  induction p with
  | base p => exact ⟨fun _ => {s | s.2 ∈ p.denote M s.1}, fun _ _ _ => le_rfl⟩
  | pred i args => exact ⟨fun η => {s | ((fun j => (args j).eval M s.1), s.2) ∈ η i},
      fun _ _ h _ hs => h i hs⟩
  | conj p q dp dq => exact ⟨fun η => dp η ∩ dq η,
      fun _ _ h _ hs => ⟨dp.monotone h hs.1, dq.monotone h hs.2⟩⟩
  | disj p q dp dq => exact ⟨fun η => dp η ∪ dq η,
      fun _ _ h _ hs => hs.elim (fun hp => Or.inl (dp.monotone h hp))
        (fun hq => Or.inr (dq.monotone h hq))⟩
  | sep p q dp dq => exact ⟨fun η => {s | ∃ a b, M.resource.join a b s.2 ∧
      (s.1, a) ∈ dp η ∧ (s.1, b) ∈ dq η}, by
      intro η ζ h s hs
      obtain ⟨a,b,hj,hp,hq⟩ := hs
      exact ⟨a,b,hj,dp.monotone h hp,dq.monotone h hq⟩⟩
  | wand p q dq => exact ⟨fun η => {s | ∀ a b, M.resource.join s.2 a b →
      a ∈ p.denote M s.1 → (s.1, b) ∈ dq η},
      fun _ _ h _ hs a b hj ha => dq.monotone h (hs a b hj ha)⟩
  | ex p dp => exact ⟨fun η => {s | ∃ x, (consValues M x s.1, s.2) ∈ dp η}, by
      intro η ζ h s hs
      obtain ⟨x,hx⟩ := hs
      exact ⟨x,dp.monotone h hx⟩⟩
  | all p dp => exact ⟨fun η => {s | ∀ x : M.Value, (consValues M x s.1, s.2) ∈ dp η},
      by
        intro η ζ h s hs x
        exact dp.monotone h (hs x)⟩
  | @lfp r k P' body args db =>
      let F (η : RelEnv M (P' ∘ Fin.succ)) (ρ : Tuple M k) :
          Set (State M (P' 0)) →o Set (State M (P' 0)) :=
        ⟨fun X => {s : State M (P' 0) | (appendValues M s.1 ρ, s.2) ∈ db (insert M P' η X)},
          fun _ _ h _ hs => db.monotone ((insert M P' η).monotone h) hs⟩
      exact ⟨fun η => {s | ((fun j => (args j).eval M s.1), s.2) ∈ (F η s.1).lfp}, by
        intro η ζ h s hs
        have hF : F η s.1 ≤ F ζ s.1 := by
          intro X x hx
          apply db.monotone ?_ hx
          intro i
          exact Fin.cases le_rfl (fun j => h j) i
        exact OrderHom.lfp.monotone hF hs⟩

end Silmaril.Logic.Separation.Parameterized
