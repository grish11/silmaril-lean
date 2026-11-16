module

public import Silmaril.Logic.STLCMatching.Native

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCMatching
open CategoryTheory Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Varying operator signatures over a fixed arbitrary set of base types. -/
structure FixedSignature (B : Type) where
  operators : List (Ty B) → Ty B → Type

abbrev FixedSignature.source {B : Type} (S : FixedSignature B) : Signature :=
  ⟨B, S.operators⟩

structure FixedHom {B : Type} (S T : FixedSignature B) where
  operators : OpMap S.source T.operators

instance {B : Type} : Category (FixedSignature B) where
  Hom := FixedHom
  id _ := ⟨fun o => o⟩
  comp f g := ⟨fun o => g.operators (f.operators o)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace FixedHom
variable {B : Type} {S T U : FixedSignature B}

def pull (f : S ⟶ T) (M : Model T.source) : Model S.source :=
  ⟨⟨M.toSetModel.base, fun o args => M.toSetModel.op (f.operators o) args⟩, M.nonempty⟩

def primitive (f : S ⟶ T) : {τ : Ty B} → Primitive S.source τ → Primitive T.source τ
  | _, .ident a => .ident (S := T.source) a
  | _, .konst a b => .konst (S := T.source) a b
  | _, .subst a b c => .subst (S := T.source) a b c
  | _, .original o => .original (f.operators o)

def native (f : S ⟶ T) : (nativeSignature S.source).symbols ⟶ (nativeSignature T.source).symbols where
  operations := fun op => match op with
    | .primitive p => .primitive (primitive f p)
    | .app a b => .app (S := T.source) a b

@[simp] theorem native_id : native (𝟙 S) = 𝟙 (nativeSignature S.source).symbols := by
  apply Algebraic.ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op with
  | primitive p => cases p <;> rfl
  | app a b => rfl

@[simp] theorem native_comp (f : S ⟶ T) (g : T ⟶ U) :
    native (S := S) (T := U) (f ≫ g) =
      native (S := S) (T := T) f ≫ native (S := T) (T := U) g := by
  apply Algebraic.ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op with
  | primitive p => cases p <;> rfl
  | app a b => rfl

private theorem model_eq {A : Algebraic.ManySorted.Signature (Ty B)}
    {M N : Matching.FirstOrder.Model A} (hc : M.carrier = N.carrier)
    (ho : HEq (@M.operation) (@N.operation)) : M = N := by
  cases M
  cases N
  cases hc
  cases ho
  rfl

theorem native_pull (f : S ⟶ T) (M : Model T.source) :
    Matching.FirstOrder.SignatureMap.reduct (native (S := S) (T := T) f) (nativeModel M) =
      nativeModel (pull f M) := by
  refine model_eq rfl (heq_of_eq ?_)
  funext n inputs output op args
  cases op with
  | primitive p => cases p <;> rfl
  | app a b => rfl

def raw (f : S ⟶ T) : Raw S.source → Raw T.source
  | .var n => .var n
  | .lam a t => .lam a (raw f t)
  | .app t u => .app (raw f t) (raw f u)
  | .op o args => .op (f.operators o) (fun i => raw f (args i))

theorem infer_raw [DecidableEq B] (f : S ⟶ T) (Γ : Ctx B) (t : Raw S.source) :
    Raw.infer Γ (raw (S := S) (T := T) f t) = Raw.infer Γ t := by
  induction t generalizing Γ with
  | var n => rfl
  | lam a t ih => simp only [raw, Raw.infer, ih]
  | app t u iht ihu =>
      simp only [raw, Raw.infer, iht, ihu]
      cases ht : Raw.infer Γ t with
      | none => simp_all
      | some a =>
          cases a with
          | base b => simp_all
          | arrow a b =>
              cases hu : Raw.infer Γ u with
              | none => simp_all
              | some c => by_cases h : a = c <;> simp_all
  | op o args ih => simp only [raw, Raw.infer, ih]

def sentence (f : S ⟶ T) : STLC.Sentence S.source → STLC.Sentence T.source
  | .typing Γ t τ => .typing Γ (raw f t) τ
  | .equation t u => .equation (t.mapOp f.operators) (u.mapOp f.operators)

theorem eval_map (f : S ⟶ T) (M : Model T.source)
    {Γ : Ctx S.source.Base} {τ : Ty S.source.Base} (t : Term S.source Γ τ)
    (ρ : Tuple (STLC.carrier M.toSetModel.base) Γ) :
    STLC.eval M.toSetModel (t.mapOp f.operators) ρ = STLC.eval (pull f M).toSetModel t ρ := by
  induction t with
  | var x => rfl
  | lam t ih => funext x; exact ih (Tuple.cons x ρ)
  | app t u iht ihu => simp only [Term.mapOp, STLC.eval, iht, ihu]; rfl
  | op o args ih => simp only [Term.mapOp, STLC.eval, ih, pull]

theorem satisfaction (f : S ⟶ T) (M : Model T.source) (p : STLC.Sentence S.source) :
    STLC.Sat M.toSetModel (sentence f p) ↔ STLC.Sat (pull f M).toSetModel p := by
  cases p with
  | typing Γ t τ =>
      classical
      change Raw.HasType (S := T.source) Γ (raw (S := S) (T := T) f t) τ ↔
        Raw.HasType (S := S.source) Γ t τ
      rw [← Raw.infer_eq_some, ← Raw.infer_eq_some, infer_raw]
  | equation t u =>
      simp only [sentence, STLC.Sat, eval_map, pull]

end FixedHom
end Silmaril.Logic.STLCMatching
