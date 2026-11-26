module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Executable typed steps for finite shaped overlay feedback -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax

universe u x y

abbrev Ty := Silmaril.Ty Empty
abbrev atomType : Unit → Empty → Prop := fun _ _ => False
abbrev Payload (A : Ty) := singlePayload (atomType := atomType) A
abbrev Bindings (Γ : List Ty) := (i : Fin Γ.length) → Payload (Γ.get i)

def emptyBindings : Bindings [] := fun i => Fin.elim0 i

def Bindings.push {Γ : List Ty} {A : Ty} (env : Bindings Γ) (a : Payload A) : Bindings (A :: Γ) :=
  Fin.cases a env

/-- Complete deterministic observations, before decoding the final sum. -/
inductive Answer (A : Ty) (states : Nat) where
  | ret (value : Payload A) (final : Fin states)
  | fault (final : Fin states)
  | diverge
  | ub

def Answer.behaviour {A : Ty} {states : Nat} : Answer A states → Behaviour 1 Unit (Fin states)
  | .ret a t => returnPayload a.val t
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}
  | .ub => ⊤

/-- Native primitives have three ordinary outcomes. Only overlay syntax
introduces fresh UB. -/
inductive StateReply (A : Ty) (σ : Type x) where
  | ret (value : Payload A) (final : σ)
  | fault (final : σ)
  | diverge

def StateReply.mapState {A : Ty} {σ : Type x} {τ : Type y} (f : σ → τ) :
    StateReply A σ → StateReply A τ
  | .ret a s => .ret a (f s)
  | .fault s => .fault (f s)
  | .diverge => .diverge

abbrev Reply (A : Ty) (states : Nat) := StateReply A (Fin states)

namespace Reply

abbrev ret {A : Ty} {states : Nat} (a : Payload A) (s : Fin states) : Reply A states := StateReply.ret a s
abbrev fault {A : Ty} {states : Nat} (s : Fin states) : Reply A states := StateReply.fault s
abbrev diverge {A : Ty} {states : Nat} : Reply A states := StateReply.diverge

end Reply

variable {Φ : Type u} [HasTy Φ Ty] {states : Nat} {σ : Type x}

/-- A deterministic primitive interpreter at exact input and reply types
over an arbitrary state carrier. -/
abbrev StatePrimitives (Φ : Type u) [HasTy Φ Ty] (σ : Type x) :=
  (f : Φ) → Payload (instrSrc f) → σ → StateReply (instrTrg f) σ

abbrev Primitives (Φ : Type u) [HasTy Φ Ty] (states : Nat) := StatePrimitives Φ (Fin states)

def StateReply.returns {A : Ty} (reply : StateReply A σ) (b : Value Unit) (t : σ) : Prop :=
  match reply with
  | .ret a s => a.val = b ∧ s = t
  | .fault _ | .diverge => False

abbrev Reply.returns {A : Ty} (reply : Reply A states) (b : Value Unit) (t : Fin states) : Prop :=
  StateReply.returns reply b t

/-- The observational model is the graph of the executable primitive
interpreter. In particular, a fault or divergence has no successful reply. -/
abbrev rawModel (prim : StatePrimitives Φ σ) {n : Nat} (bound : Fin n → Value Unit) :
    Institution.Observational.Model Φ n where
  α := Unit
  σ := σ
  instr := fun f a s b t => ∃ h : Shape.ValueTyped atomType a (instrSrc f),
    (prim f ⟨a, h⟩ s).returns b t
  faults := fun f a s t => ∃ h : Shape.ValueTyped atomType a (instrSrc f),
    prim f ⟨a, h⟩ s = .fault t
  prim := fun f a s => ∃ h : Shape.ValueTyped atomType a (instrSrc f),
    prim f ⟨a, h⟩ s = .diverge
  bound := bound

abbrev model (prim : StatePrimitives Φ σ) {Γ : List Ty} (env : Bindings Γ) :
    Shape.Model Φ Γ where
  raw := rawModel prim fun i => (env i).val
  atomType := atomType
  boundTyped i := (env i).property
  instrTyped := by
    intro f a s b t _ ⟨ha, hr⟩
    cases h : prim f ⟨a, ha⟩ s with
    | ret value _ =>
      rw [h] at hr
      exact hr.1 ▸ value.property
    | fault | diverge => rw [h] at hr; exact hr.elim

/-- The executable constructor expressions of this fragment. -/
inductive Expr (Γ : List Ty) : Ty → Type where
  | var (i : Fin Γ.length) : Expr Γ (Γ.get i)
  | unit : Expr Γ .unit
  | pair {A B} : Expr Γ A → Expr Γ B → Expr Γ (.product A B)
  | inl {A B} : Expr Γ A → Expr Γ (.coprod A B)
  | inr {A B} : Expr Γ B → Expr Γ (.coprod A B)

namespace Expr

variable {Γ : List Ty} {A : Ty}

def term : {A : Ty} → Expr Γ A → LambdaSSA.Tm Φ
  | _, .var i => .var i
  | _, .unit => .unit
  | _, .pair a b => .pair a.term b.term
  | _, .inl a => .inl a.term
  | _, .inr a => .inr a.term

theorem typed (a : Expr Γ A) : (a.term (Φ := Φ)).HasType Γ A := by
  induction a with
  | var i => exact .var (List.getElem?_eq_getElem i.isLt)
  | unit => exact .unit
  | pair _ _ ha hb => exact .pair ha hb
  | inl _ ha => exact .inl ha
  | inr _ ha => exact .inr ha

def eval (env : Bindings Γ) : {A : Ty} → Expr Γ A → Payload A
  | _, .var i => env i
  | _, .unit => ⟨.unit, .unit⟩
  | _, .pair a b => pairPayload (a.eval env) (b.eval env)
  | _, .inl a => ⟨.inl (a.eval env).val, .inl (a.eval env).property⟩
  | _, .inr a => ⟨.inr (a.eval env).val, .inr (a.eval env).property⟩

end Expr

/-- Typed, acyclic overlay steps. Calls bind their successful reply and cases
bind the payload of the selected tag. The outer loop is existing feedback. -/
inductive Program (Φ : Type u) [HasTy Φ Ty] : List Ty → Ty → Type u where
  | ret {Γ A} : Expr Γ A → Program Φ Γ A
  | ub {Γ A} : Program Φ Γ A
  | call {Γ A} (f : Φ) : Expr Γ (instrSrc f) → Program Φ (instrTrg f :: Γ) A → Program Φ Γ A
  | case {Γ A B C} : Expr Γ (.coprod A B) → Program Φ (A :: Γ) C →
      Program Φ (B :: Γ) C → Program Φ Γ C

namespace Program

variable {Γ : List Ty} {A B : Ty}

def returnRegion (a : Expr Γ A) : LambdaSSA.UB.Typed (Φ := Φ) Γ [A] :=
  ⟨.br 0 a.term, .br (ℓ := 0) rfl a.typed⟩

def requestRegion (f : Φ) (a : Expr Γ (instrSrc f)) : LambdaSSA.UB.Typed (Φ := Φ) Γ [instrTrg f] :=
  ⟨.br 0 (.op f a.term), .br (ℓ := 0) rfl (.op (f := f) a.typed)⟩

def caseRegion (a : Expr Γ (.coprod A B)) : LambdaSSA.UB.Typed (Φ := Φ) Γ [A, B] :=
  ⟨.case a.term (.br 0 (.var 0)) (.br 1 (.var 0)),
    .case a.typed (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (.br (ℓ := 1) rfl (.var (i := 0) rfl))⟩

/-- Elaborate directly into existing native branch/case syntax, typed overlay
label substitution, and literal overlay UB. -/
def region : {Γ : List Ty} → Program Φ Γ A → Region Φ Γ [A]
  | _, .ret a => .native (returnRegion a)
  | _, .ub => .ub
  | _, .call f arg body => .lsubst (.native (requestRegion f arg)) fun i => by
      obtain rfl := Fin.eq_zero i
      exact body.region
  | Γ, .case (A := L) (B := R) arg left right =>
    .lsubst (.native (caseRegion arg))
      (Fin.cases (motive := fun i => Region Φ ([L, R].get i :: Γ) [A]) left.region
        (fun i => by obtain rfl := Fin.eq_zero i; exact right.region))

/-- Evaluate a step structurally without a fuel argument. Only a successful
instruction reply evaluates its continuation at the final machine state. -/
def eval (prim : Primitives Φ states) :
    {Γ : List Ty} → Bindings Γ → Fin states → Program Φ Γ A → Answer A states
  | _, env, s, .ret a => .ret (a.eval env) s
  | _, _, _, .ub => .ub
  | _, env, s, .call f arg body =>
    match prim f (arg.eval env) s with
    | .ret a t => body.eval prim (env.push a) t
    | .fault t => .fault t
    | .diverge => .diverge
  | _, env, s, .case arg left right =>
    match splitPayload (arg.eval env) with
    | .inl a => left.eval prim (env.push a) s
    | .inr b => right.eval prim (env.push b) s

end Program

variable {X A B : Ty} {captures seeds results : Nat}

/-- Capture codes select the supported starts. Complete seed/result codes
give an index to every typed reply of a generated step. -/
structure Codes (X A B : Ty) (captures seeds results : Nat) where
  capture : Fin captures → Payload X
  seed : Fin seeds ≃ Payload A
  result : Fin results ≃ Payload B

def Codes.carrier (codes : Codes X A B captures seeds results) (prim : Primitives Φ states) :
    Carrier (model prim emptyBindings) X A B captures (seeds * states) results states where
  capture := codes.capture
  invocation p :=
    let (a, s) := finProdFinEquiv.symm p
    (codes.seed a, s)
  result := codes.result.toEmbedding
  final := Function.Embedding.refl (Fin states)

def Answer.row (codes : Codes X A B captures seeds results) :
    Answer (.coprod B A) states → Row (seeds * states) results states
  | .ret a t =>
    match splitPayload a with
    | .inl b => .stop (.ret (codes.result.symm b) t)
    | .inr a => .repeat (finProdFinEquiv (codes.seed.symm a, t))
  | .fault t => .stop (.fault t)
  | .diverge => .stop .diverge
  | .ub => .stop .ub

/-- Generate the table compared by the existing finite feedback checker. -/
def generate (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (body : Program Φ [A, X] (.coprod B A)) : Table captures (seeds * states) results states :=
  fun c p =>
    let (a, s) := (codes.carrier prim).invocation p
    (body.eval prim ((emptyBindings.push (codes.capture c)).push a) s).row codes

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
