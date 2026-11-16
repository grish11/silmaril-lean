module

public import Silmaril.Logic.Separation.Parameterized.Institution.Defs
public import Silmaril.Logic.FirstOrderLFP.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples

inductive TargetSort where
  | value
  | heap

def pointerHeapTargetSorts (n : Nat) : Fin (n + 1) → TargetSort :=
  Fin.cases .heap (fun _ => .value)

inductive Operation (A : Signature) : (n : Nat) → (Fin n → TargetSort) → TargetSort → Type where
  | value {n} (o : A.Op n) : Operation A n (fun _ => .value) .value
  | unit : Operation A 0 (fun _ => .heap) .heap

inductive Relation (A : Signature) : (n : Nat) → (Fin n → TargetSort) → Type where
  | atom {n} (a : A.Atom n) : Relation A (n + 1) (pointerHeapTargetSorts n)
  | join : Relation A 3 (fun _ => .heap)

def signature (A : Signature) : FOL.Signature where
  S := TargetSort
  Op := Operation A
  Rel := Relation A

def carrier {A : Signature} (M : Model A) : TargetSort → Type
  | .value => M.Value
  | .heap => M.resource.carrier

/-- No finite-heap or inhabited-value premise: the target interprets the exact
source carrier, source joins and source indexed ownership predicates. -/
def model {A : Signature} (M : Model A) : Silmaril.Logic.FirstOrderLFP.Model (signature A) where
  toStructure := {
    carrier := carrier M
    op := fun o args => match o with
      | .value o => M.operation o args
      | .unit => M.resource.unit
    rel := fun r args => match r with
      | .atom a => args 0 ∈ M.atom a (fun i => args i.succ)
      | .join => M.resource.join (args 0) (args 1) (args 2)
  }

abbrev profile (A : Signature) (n : Nat) : Silmaril.Logic.FirstOrderLFP.Profile (signature A) :=
  ⟨n + 1,pointerHeapTargetSorts n⟩

/-- Bound recursive tuples contain a heap first, followed by pointer values. -/
def encodeState {A : Signature} (M : Model A) {n} (s : State M n) :
    Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n) :=
  Fin.cases s.2 s.1

def decodeState {A : Signature} (M : Model A) {n}
    (x : Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n)) : State M n :=
  ⟨fun i => x i.succ,x 0⟩

def stateEquiv {A : Signature} (M : Model A) (n : Nat) :
    State M n ≃ Silmaril.Logic.FirstOrderLFP.Tuple (model M) (profile A n) where
  toFun := encodeState M
  invFun := decodeState M
  left_inv _ := rfl
  right_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Encoding all recursive predicates is inverse image along a tuple bijection. -/
def encodeRelEnv {A : Signature} (M : Model A) {r} {P : Fin r → Nat}
    (η : RelEnv M P) : Silmaril.Logic.FirstOrderLFP.RelEnv (model M) (fun i => profile A (P i)) :=
  fun i => {x | decodeState M x ∈ η i}

/-- Source terms compile against arbitrary target value terms. This permits
object binders and captured ambient parameters without an empty-context trick. -/
def term {A : Signature} {k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → EQ.Term (signature A).toSignature Γ .value) :
    Term A k → EQ.Term (signature A).toSignature Γ .value
  | .var i => σ i
  | .app o args => .app (.value o) (fun i => term σ (args i))

theorem eval_term {A : Signature} (M : Model A) {k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → EQ.Term (signature A).toSignature Γ .value) (t : Term A k)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    (term σ t).eval (model M).toStructure.toAlgebra θ =
      t.eval M (fun i => (σ i).eval (model M).toStructure.toAlgebra θ) := by
  induction t with
  | var i => rfl
  | app o args ih =>
      change M.operation o (fun i => (term σ (args i)).eval _ θ) = _
      exact congrArg (M.operation o) (funext ih)

/-- Context substitution on public sorted terms; signatures are unchanged. -/
def substitute {S : EQ.Signature} {k l} {Γ : Fin k → S.S} {Δ : Fin l → S.S}
    (σ : ∀ i, EQ.Term S Δ (Γ i)) : {s : S.S} → EQ.Term S Γ s → EQ.Term S Δ s
  | _, .var i => σ i
  | _, .app o args => .app o (fun i => substitute σ (args i))

theorem eval_substitute {S : EQ.Signature} (M : EQ.Algebra S) {k l}
    {Γ : Fin k → S.S} {Δ : Fin l → S.S} (σ : ∀ i, EQ.Term S Δ (Γ i))
    {s : S.S} (t : EQ.Term S Γ s) (θ : ∀ i, M.carrier (Δ i)) :
    (substitute σ t).eval M θ = t.eval M (fun i => (σ i).eval M θ) := by
  induction t with
  | var i => rfl
  | app o args ih => exact congrArg (M.op o) (funext ih)

def contextCons {α : Type} {k} (s : α) (Γ : Fin k → α) : Fin (k+1) → α :=
  Fin.cases s Γ

/-- Fresh binder at zero; ambient terms shift to successor indices. -/
def liftTerm {S : EQ.Signature} {k} {Γ : Fin k → S.S} (s : S.S) {t : S.S}
    (u : EQ.Term S Γ t) : EQ.Term S (contextCons s Γ) t :=
  substitute (fun i => EQ.Term.var i.succ) u

theorem eval_liftTerm {S : EQ.Signature} (M : EQ.Algebra S) {k}
    {Γ : Fin k → S.S} (s : S.S) {t : S.S} (u : EQ.Term S Γ t)
    (x : M.carrier s) (θ : ∀ i, M.carrier (Γ i)) :
    (liftTerm s u).eval M (Fin.cases (motive := fun i => M.carrier (contextCons s Γ i)) x θ) = u.eval M θ := by
  exact eval_substitute M _ u (Fin.cases (motive := fun i => M.carrier (contextCons s Γ i)) x θ)

/-- Every actual source homomorphism gives an ordinary FOL structure
homomorphism. This does not assert a lift into FO(LFP)'s equality-only model
category, whose arrows require equal structures. -/
def structureHom {A : Signature} {M N : Model A} (f : Model.Hom M N) :
    FOL.Structure.Hom (model M).toStructure (model N).toStructure where
  map s := match s with
    | .value => f.value
    | .heap => f.resource
  map_op := by
    intro n w s o args
    cases o with
    | value o => exact f.operation o args
    | unit => exact f.unit
  map_rel := by
    intro n w r args h
    cases r with
    | atom a => exact f.atom a (fun i => args i.succ) h
    | join => exact f.join h

end Silmaril.Logic.Separation.Parameterized.FirstOrder
