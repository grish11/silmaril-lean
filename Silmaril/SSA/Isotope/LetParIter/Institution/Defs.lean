module

public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs
public import Silmaril.SSA.Isotope.Institution.Signature.Thms
public import Silmaril.Logic.Institution.Room

/-! # Native LetParIter equations and models

Signatures are the native instruction signatures over fixed types and effects.
A room fixes the native value-type model, so that contexts, products, and sums
use the same values on both sides of a strict model arrow. The computations,
iteration, instructions, and parallel pairing are supplied by each model.
-/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Institution

open CategoryTheory Parallel LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.Institution (InstrSig)

universe u v w

variable {τ ε : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]

/-- A term with its exact derivation, including the intermediate types chosen
at binders. The two contexts and the result type are fixed. -/
structure Expr (P : InstrSig τ ε) (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (A : τ) where
  term : Tm ν P.Instr n
  typing : Derivation P.Instr Γ β term A

namespace Expr

variable {P Q : InstrSig τ ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A B : τ}

def cast (h : A = B) (a : Expr P Γ β A) : Expr P Γ β B := h ▸ a

/-- Apply an instruction to an expression at its declared source type. -/
def op (f : P.Instr) (a : Expr P Γ β (instrSrc f)) : Expr P Γ β (instrTrg f) :=
  ⟨_, .op a.typing⟩

/-- Transport the exact input and output indices across the signature map. -/
def relabelOp (σ : P ⟶ Q) (f : P.Instr) (a : Expr Q Γ β (instrSrc f)) :
    Expr Q Γ β (instrTrg f) :=
  (op (σ.instr f) (a.cast (σ.source f).symm)).cast (σ.target f)

def let₁ (a : Expr P Γ β A) (b : Expr P Γ (.snoc β A) B) : Expr P Γ β B :=
  ⟨_, .let₁ a.typing b.typing⟩

def pair (a : Expr P Γ β A) (b : Expr P Γ β B) : Expr P Γ β (product A B) :=
  ⟨_, .pair a.typing b.typing⟩

def let₂ {C : τ} (a : Expr P Γ β (product A B)) (b : Expr P Γ (.snoc (.snoc β A) B) C) :
    Expr P Γ β C :=
  ⟨_, .let₂ a.typing b.typing⟩

def inl {h : Tier.HasCase .iter} (a : Expr P Γ β A) : Expr P Γ β (CaseTypes.sum h A B) :=
  ⟨_, .inl a.typing⟩

def inr {h : Tier.HasCase .iter} (b : Expr P Γ β B) : Expr P Γ β (CaseTypes.sum h A B) :=
  ⟨_, .inr b.typing⟩

def case {C : τ} {h : Tier.HasCase .iter} (e : Expr P Γ β (CaseTypes.sum h A B))
    (l : Expr P Γ (.snoc β A) C) (r : Expr P Γ (.snoc β B) C) : Expr P Γ β C :=
  ⟨_, .case e.typing l.typing r.typing⟩

def abort {h : Tier.HasCase .iter} (a : Expr P Γ β (CaseTypes.zero h)) : Expr P Γ β A :=
  ⟨_, .abort a.typing⟩

def iter {h : Tier.HasIter .iter} (a : Expr P Γ β A)
    (b : Expr P Γ (.snoc β A) (CaseTypes.sum (Tier.iterHasCase h) B A)) : Expr P Γ β B :=
  ⟨_, .iter (h := h) a.typing b.typing⟩

def par (a : Expr P Γ β A) (b : Expr P Γ β B) : Expr P Γ β (product A B) :=
  ⟨_, .par a.typing b.typing⟩

/-- Relabel instructions in an exact derivation, retaining every binder index. -/
def mapDerivation (σ : P ⟶ Q) {Γ : Ctx ν τ} :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν P.Instr n} → {A : τ} →
    Derivation P.Instr Γ β t A → Expr Q Γ β A
  | _, _, _, _, .fv h => ⟨_, .fv h⟩
  | _, _, _, _, .bv => ⟨_, .bv⟩
  | _, _, _, _, .op (f := f) ha => relabelOp σ f (mapDerivation σ ha)
  | _, _, _, _, .let₁ ha hb => let₁ (mapDerivation σ ha) (mapDerivation σ hb)
  | _, _, _, _, .unit => ⟨_, .unit⟩
  | _, _, _, _, .pair ha hb => pair (mapDerivation σ ha) (mapDerivation σ hb)
  | _, _, _, _, .let₂ ha hb => let₂ (mapDerivation σ ha) (mapDerivation σ hb)
  | _, _, _, _, .inl ha => inl (mapDerivation σ ha)
  | _, _, _, _, .inr hb => inr (mapDerivation σ hb)
  | _, _, _, _, .case he hl hr =>
      Expr.case (mapDerivation σ he) (mapDerivation σ hl) (mapDerivation σ hr)
  | _, _, _, _, .abort ha => abort (mapDerivation σ ha)
  | _, _, _, _, .iter (h := h) ha hb => iter (h := h) (mapDerivation σ ha) (mapDerivation σ hb)
  | _, _, _, _, .par ha hb => par (mapDerivation σ ha) (mapDerivation σ hb)
termination_by structural _ _ _ _ d => d

def map (σ : P ⟶ Q) (a : Expr P Γ β A) : Expr Q Γ β A := mapDerivation σ a.typing

end Expr

/-- Both sides of a sentence have the same free and bound contexts and the
same result type. Its truth is equality of native computations at every environment. -/
structure Sentence (P : InstrSig τ ε) (ν : Type w) [DecidableEq ν] where
  Γ : Ctx ν τ
  n : Nat
  β : BoundCtx τ n
  A : τ
  lhs : Expr P Γ β A
  rhs : Expr P Γ β A

def Sentence.map {P Q : InstrSig τ ε} (σ : P ⟶ Q) (s : Sentence P ν) : Sentence Q ν :=
  ⟨s.Γ, s.n, s.β, s.A, s.lhs.map σ, s.rhs.map σ⟩

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

/-- A native instruction interpretation with lawful monadic sequencing and
Elgot iteration, and an independently chosen symmetric parallel pairing. -/
structure Model (P : InstrSig τ ε) where
  Carrier : Type v → Type v
  [monad : Monad Carrier]
  [lawfulMonad : LawfulMonad Carrier]
  [iterate : Elgot.Iterate Carrier]
  [lawfulElgot : Elgot.LawfulElgotMonad Carrier]
  pairing : Elgot.ParallelPairing Carrier
  instructions : InstructionModel P.Instr τ ε Carrier

attribute [instance] Model.monad Model.lawfulMonad Model.iterate Model.lawfulElgot

namespace Model

variable {P Q : InstrSig τ ε}

abbrev pure (M : Model P) {X : Type v} (x : X) : M.Carrier X :=
  letI := M.monad
  Pure.pure x

abbrev bind (M : Model P) {X Y : Type v} (x : M.Carrier X) (k : X → M.Carrier Y) :
    M.Carrier Y :=
  letI := M.monad
  Bind.bind x k

abbrev iter (M : Model P) {X Y : Type v} (f : X → M.Carrier (Y ⊕ X)) (x : X) :
    M.Carrier Y :=
  letI := M.iterate
  Elgot.iter f x

/-- An arrow acts on computations at each value type. Since the value model
is fixed, ordinary pure instruction functions must agree. Their agreement
does not require the target's monadic `pure` to be injective. -/
structure Hom (M N : Model P) where
  app {X : Type v} : M.Carrier X → N.Carrier X
  map_pure {X : Type v} (x : X) : app (M.pure x) = N.pure x
  map_bind {X Y : Type v} (x : M.Carrier X) (k : X → M.Carrier Y) :
    app (M.bind x k) = N.bind (app x) (fun a => app (k a))
  map_iter {X Y : Type v} (f : X → M.Carrier (Y ⊕ X)) (x : X) :
    app (M.iter f x) = N.iter (fun a => app (f a)) x
  map_pair {X Y : Type v} (x : M.Carrier X) (y : M.Carrier Y) :
    app (M.pairing.pair x y) = N.pairing.pair (app x) (app y)
  map_instr (f : P.Instr) (a : TyDen (instrSrc (τ := τ) f)) :
    app (M.instructions.denote f a) = N.instructions.denote f a
  map_pureInstr (f : P.Instr) (hf : IsPure (⊥ : ε) f) (a : TyDen (instrSrc (τ := τ) f)) :
    M.instructions.denotePure f hf a = N.instructions.denotePure f hf a

@[ext] theorem Hom.ext {M N : Model P} {f g : Hom M N} (h : @f.app = @g.app) : f = g := by
  cases f; cases g; cases h
  rfl

instance : Category (Model P) where
  Hom := Hom
  id _ := ⟨id, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ => rfl⟩
  comp f g :=
    { app := fun a => g.app (f.app a)
      map_pure := fun a => (congrArg g.app (f.map_pure a)).trans (g.map_pure a)
      map_bind := fun x k => (congrArg g.app (f.map_bind x k)).trans (g.map_bind _ _)
      map_iter := fun h x => (congrArg g.app (f.map_iter h x)).trans (g.map_iter _ _)
      map_pair := fun x y => (congrArg g.app (f.map_pair x y)).trans (g.map_pair (f.app x) (f.app y))
      map_instr := fun f' a => (congrArg g.app (f.map_instr f' a)).trans (g.map_instr f' a)
      map_pureInstr := fun f' hf a => (f.map_pureInstr f' hf a).trans (g.map_pureInstr f' hf a) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem comp_app {M N K : Model P} (F : M ⟶ N) (G : N ⟶ K)
    {X : Type v} (x : M.Carrier X) : (F ≫ G).app x = G.app (F.app x) := rfl

/-- Change the type index of a native value or computation along an exact equality. -/
def transport (D : τ → Sort w) {A B : τ} (h : A = B) (x : D A) : D B :=
  Eq.ndrec (motive := D) x h

theorem transport_pure (M : Model P) {A B : τ} (h : A = B) (x : TyDen A) :
    transport (fun T => M.Carrier (TyDen T)) h (M.pure x) = M.pure (transport TyDen h x) := by
  cases h
  rfl

/-- The operation denotation after restriction of the instruction signature. -/
def restrictInstr (σ : P ⟶ Q) (M : Model Q) (f : P.Instr)
    (a : TyDen (instrSrc (τ := τ) f)) : M.Carrier (TyDen (instrTrg (τ := τ) f)) :=
  transport (fun T => M.Carrier (TyDen T)) (σ.target f)
    (M.instructions.denote (σ.instr f) (transport TyDen (σ.source f).symm a))

/-- The ordinary function on values after restriction, with the same bottom effect. -/
def restrictPureInstr (σ : P ⟶ Q) (M : Model Q) (f : P.Instr)
    (hf : IsPure (⊥ : ε) f) (a : TyDen (instrSrc (τ := τ) f)) : TyDen (instrTrg (τ := τ) f) :=
  transport TyDen (σ.target f)
    (M.instructions.denotePure (σ.instr f) ((σ.effect f).trans hf)
      (transport TyDen (σ.source f).symm a))

/-- Restrict both parts of the instruction model while retaining all structural operations. -/
def reduct (σ : P ⟶ Q) (M : Model Q) : Model P where
  Carrier := M.Carrier
  monad := M.monad
  lawfulMonad := M.lawfulMonad
  iterate := M.iterate
  lawfulElgot := M.lawfulElgot
  pairing := M.pairing
  instructions :=
    { denote := M.restrictInstr σ
      denotePure := M.restrictPureInstr σ
      denote_pure f hf a :=
        (congrArg (transport _ (σ.target f)) (M.instructions.denote_pure
          (σ.instr f) ((σ.effect f).trans hf) (transport TyDen (σ.source f).symm a))).trans
          (transport_pure M (σ.target f) _) }

theorem transport_app {M N : Model P} (F : Model.Hom M N) {A B : τ} (h : A = B)
    (x : M.Carrier (TyDen A)) :
    F.app (transport (fun T => M.Carrier (TyDen T)) h x) =
      transport (fun T => N.Carrier (TyDen T)) h (F.app x) := by
  cases h
  rfl

/-- Restriction preserves the underlying computation map and all structural laws. -/
def reductHom (σ : P ⟶ Q) {M N : Model Q} (F : Model.Hom M N) :
    Model.Hom (reduct σ M) (reduct σ N) where
  app := F.app
  map_pure := F.map_pure
  map_bind := F.map_bind
  map_iter := F.map_iter
  map_pair := F.map_pair
  map_instr f a := by
    change F.app (M.restrictInstr σ f a) = N.restrictInstr σ f a
    unfold Model.restrictInstr
    rw [transport_app, F.map_instr]
  map_pureInstr f hf a :=
    congrArg (transport TyDen (σ.target f))
      (F.map_pureInstr (σ.instr f) ((σ.effect f).trans hf)
        (transport TyDen (σ.source f).symm a))

/-- Interpret the exact derivation using the native LetParIter evaluator. -/
def eval (M : Model P) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}
    (a : Expr P Γ β A) (γ : CtxDen Γ) (ρ : BoundDen β) : M.Carrier (TyDen A) :=
  letI := M.monad
  letI := M.iterate
  letI := M.instructions
  LetParIter.denote (ε := ε) M.pairing a.typing γ ρ

end Model

/-- Restriction acts contravariantly on model categories. -/
def reductFunctor {P Q : InstrSig τ ε} (σ : P ⟶ Q) : Model Q ⥤ Model P where
  obj := Model.reduct σ
  map := Model.reductHom σ
  map_id _ := rfl
  map_comp _ _ := rfl



/-- A model satisfies the equation when the two native computations coincide
for all values of both contexts. -/
def Sat {P : InstrSig τ ε} (M : Model P) (s : Sentence P ν) : Prop :=
  ∀ (γ : CtxDen s.Γ) (ρ : BoundDen s.β), M.eval s.lhs γ ρ = M.eval s.rhs γ ρ

end Silmaril.Isotope.LetParIter.Institution
