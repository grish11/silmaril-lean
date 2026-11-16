module

public import Silmaril.Calculi.LambdaCube.STLC.Thms
public import Silmaril.Logic.Matching.SortMaps.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCMatching
open CategoryTheory Silmaril.Calculi.TypedLambda
open Cslib.LambdaCalculus.LocallyNameless.Stlc
open Silmaril.Calculi.LambdaCube

/-- The source restriction is a property of actual public set models. -/
structure Model (S : Signature) where
  toSetModel : STLC.SetModel S
  nonempty : ∀ b, Nonempty (toSetModel.base b)

instance (S : Signature) : Category (Model S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

def reduct {S T : Signature} (f : STLC.SigMap S T) (M : Model T) : Model S :=
  ⟨STLC.reduct f M.toSetModel, fun b => M.nonempty (f.base b)⟩

def curryTy {B : Type} : List (Ty B) → Ty B → Ty B
  | [], τ => τ
  | a :: as, τ => .arrow a (curryTy as τ)

def curryValue {B : Type} (base : B → Type) : {as : List (Ty B)} → {τ : Ty B} →
    (Tuple (STLC.carrier base) as → STLC.carrier base τ) →
      STLC.carrier base (curryTy as τ)
  | [], _, f => f Tuple.nil
  | _ :: _, _, f => fun a => curryValue base (fun args => f (Tuple.cons a args))

/-- Typed combinator constants, independent of source lambda terms. -/
inductive Primitive (S : Signature) : Ty S.Base → Type where
  | ident (a) : Primitive S (.arrow a a)
  | konst (a b) : Primitive S (.arrow a (.arrow b a))
  | subst (a b c) : Primitive S
      (.arrow (.arrow a (.arrow b c)) (.arrow (.arrow a b) (.arrow a c)))
  | original {as τ} (op : S.Op as τ) : Primitive S (curryTy as τ)

def Primitive.eval {S : Signature} (M : STLC.SetModel S) :
    {τ : Ty S.Base} → Primitive S τ → STLC.carrier M.base τ
  | _, .ident _ => fun x => x
  | _, .konst _ _ => fun x _ => x
  | _, .subst _ _ _ => fun f g x => f x (g x)
  | _, .original op => curryValue M.base (M.op op)

inductive Comb (S : Signature) : Ctx S.Base → Ty S.Base → Type where
  | var {Γ τ} : Var Γ τ → Comb S Γ τ
  | primitive {Γ τ} : Primitive S τ → Comb S Γ τ
  | app {Γ a b} : Comb S Γ (.arrow a b) → Comb S Γ a → Comb S Γ b

def Comb.eval {S : Signature} (M : STLC.SetModel S) : {Γ : Ctx S.Base} →
    {τ : Ty S.Base} → Comb S Γ τ → Tuple (STLC.carrier M.base) Γ →
      STLC.carrier M.base τ
  | _, _, .var x, ρ => ρ _ x
  | _, _, .primitive p, _ => p.eval M
  | _, _, .app f a, ρ => f.eval M ρ (a.eval M ρ)

/-- Eliminate precisely the innermost variable using typed S/K/I. -/
def Comb.abstract {S : Signature} {Γ : Ctx S.Base} {a : Ty S.Base} :
    {b : Ty S.Base} → Comb S (a :: Γ) b → Comb S Γ (.arrow a b)
  | _, .var .zero => .primitive (.ident a)
  | _, .var (.succ x) => .app (.primitive (.konst _ a)) (.var x)
  | _, .primitive p => .app (.primitive (.konst _ a)) (.primitive p)
  | _, .app f x => .app (.app (.primitive (.subst _ _ _)) f.abstract) x.abstract

theorem Comb.eval_abstract {S : Signature} (M : STLC.SetModel S)
    {Γ : Ctx S.Base} {a b : Ty S.Base} (t : Comb S (a :: Γ) b)
    (ρ : Tuple (STLC.carrier M.base) Γ) (x : STLC.carrier M.base a) :
    t.abstract.eval M ρ x = t.eval M (Tuple.cons x ρ) := by
  induction t with
  | var v => cases v <;> simp [Comb.abstract, Comb.eval, Primitive.eval, Tuple.cons]
  | primitive p => simp [Comb.abstract, Comb.eval, Primitive.eval]
  | app f a ihf iha => simp only [Comb.abstract, Comb.eval, Primitive.eval, ihf, iha]

def Comb.applyArgs {S : Signature} {Γ : Ctx S.Base} {τ : Ty S.Base} :
    {as : List (Ty S.Base)} → Comb S Γ (curryTy as τ) →
      Tuple (Comb S Γ) as → Comb S Γ τ
  | [], f, _ => f
  | _ :: _, f, args => applyArgs (.app f (args _ .zero)) (fun _ x => args _ (.succ x))

theorem Comb.eval_applyArgs {S : Signature} (M : STLC.SetModel S)
    {Γ : Ctx S.Base} {τ : Ty S.Base} {as : List (Ty S.Base)}
    (f : Tuple (STLC.carrier M.base) as → STLC.carrier M.base τ)
    (t : Comb S Γ (curryTy as τ)) (args : Tuple (Comb S Γ) as)
    (ρ : Tuple (STLC.carrier M.base) Γ)
    (h : t.eval M ρ = curryValue M.base f) :
    (t.applyArgs args).eval M ρ = f (fun _ x => (args _ x).eval M ρ) := by
  induction as with
  | nil =>
      have he : (fun a x => (args a x).eval M ρ) = Tuple.nil :=
        Tuple.ext fun _ x => x.elim
      simpa [Comb.applyArgs, curryTy, curryValue, he] using h
  | cons a as ih =>
      have he : (fun a x => (args a x).eval M ρ) =
          Tuple.cons ((args _ .zero).eval M ρ) (fun _ x => (args _ (.succ x)).eval M ρ) := by
        apply Tuple.ext
        intro a x
        cases x <;> rfl
      rw [he]
      exact ih (fun xs => f (Tuple.cons ((args _ .zero).eval M ρ) xs))
        (.app t (args _ .zero)) (fun _ x => args _ (.succ x))
        (by
          rw [Comb.eval.eq_def]
          exact congrFun h ((args _ .zero).eval M ρ))

/-- Lambda elimination; source operators are curried, then fully applied. -/
def compile {S : Signature} : {Γ : Ctx S.Base} → {τ : Ty S.Base} →
    Term S Γ τ → Comb S Γ τ
  | _, _, .var x => .var x
  | _, _, .lam t => (compile t).abstract
  | _, _, .app f a => .app (compile f) (compile a)
  | _, _, .op o args => Comb.applyArgs (.primitive (.original o)) (fun _ x => compile (args _ x))

theorem eval_compile {S : Signature} (M : STLC.SetModel S)
    {Γ : Ctx S.Base} {τ : Ty S.Base} (t : Term S Γ τ)
    (ρ : Tuple (STLC.carrier M.base) Γ) :
    (compile t).eval M ρ = STLC.eval M t ρ := by
  induction t with
  | var x => simp [compile, Comb.eval, STLC.eval]
  | lam t ih =>
      funext x
      exact (Comb.eval_abstract M (compile t) ρ x).trans (ih (Tuple.cons x ρ))
  | app f a ihf iha => simp only [compile, Comb.eval, STLC.eval, ihf, iha]
  | op o args ih =>
      rw [compile, Comb.eval_applyArgs M (M.op o) _ _ ρ (by simp [Comb.eval, Primitive.eval])]
      change M.op o (fun _ x => (compile (args _ x)).eval M ρ) = _
      simp only [ih, STLC.eval]

end Silmaril.Logic.STLCMatching
