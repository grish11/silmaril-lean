module

public import Silmaril.SSA.Isotope.LetParIter.Substitution.Defs

/-! # The generated proof-relevant congruence for LetParIter -/

@[expose] public section

set_option autoImplicit true

namespace Silmaril.Isotope.LetParIter

open Parallel

universe u v w r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]
namespace Typing

variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

variable {p : Tm ν Φ n} {A B C : τ}

/-- The value introduced by the most recent binder. -/
def newest : Derivation Φ Γ (.snoc β A) (.bv 0 : Tm ν Φ (n + 1)) A :=
  .bv (i := 0)

def swap (d : Derivation Φ Γ β p (product A B)) :
    Derivation Φ Γ β (Parallel.Tm.swap p) (product B A) :=
  .let₂ d (.pair .bv .bv)

def assoc (d : Derivation Φ Γ β p (product (product A B) C)) :
    Derivation Φ Γ β (Parallel.Tm.assoc p) (product A (product B C)) :=
  .let₂ d (.let₂ .bv (.pair .bv (.pair .bv .bv)))

def dropRight (d : Derivation Φ Γ β p (product A unit)) :
    Derivation Φ Γ β (Parallel.Tm.dropRight p) A :=
  .let₂ d .bv

def dropLeft (d : Derivation Φ Γ β p (product unit A)) :
    Derivation Φ Γ β (Parallel.Tm.dropLeft p) A :=
  .let₂ d .bv

/-- Transport the continue summand of a loop body along the state map.
The returned value passes through unchanged. -/
def uniformityLeft {h b : Tm ν Φ (n + 1)} {A A' B : τ}
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (dh : Derivation Φ Γ (.snoc β A) h A') :
    Derivation Φ Γ (.snoc β A)
      (.case hasCase b (.inl hasCase (.bv 0)) (.inr hasCase h.underBinder)) (coprod B A') :=
  .case db (.inl newest) (.inr (underBinder dh))

/-- Evaluate the other body at the mapped state in the original environment. -/
def uniformityRight {h b' : Tm ν Φ (n + 1)} {A A' B : τ}
    (db' : Derivation Φ Γ (.snoc β A') b' (coprod B A'))
    (dh : Derivation Φ Γ (.snoc β A) h A') :
    Derivation Φ Γ (.snoc β A) (b'.underBinder.instantiate h) (coprod B A') :=
  instantiate (underBinder db') dh

end Typing

set_option backward.isDefEq.respectTransparency false in
set_option genSizeOf false in
/-- The least equivalence on typing derivations closed under the displayed
constructors, typed renaming and simultaneous pure bound substitution. Native
equations enter with their original proof-relevant witnesses at exact endpoints. -/
inductive Equiv (pureEff : ε) (Γ : Ctx ν τ) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
      Derivation Φ Γ β a A → Derivation Φ Γ β b A → Prop where
  | refl (d : Derivation Φ Γ β a A) : Equiv pureEff Γ d d
  | symm : Equiv pureEff Γ da db → Equiv pureEff Γ db da
  | trans : Equiv pureEff Γ da db → Equiv pureEff Γ db dc → Equiv pureEff Γ da dc
  | native (da : LetIter.LocallyNameless.Derivation Φ Γ β a A)
      (db : LetIter.LocallyNameless.Derivation Φ Γ β b A) :
      LetIter.ProofRelevant.LocallyNameless.TypedEquiv.Related pureEff Γ
        (nativeTyping da) (nativeTyping db) →
      Equiv pureEff Γ (derivation da) (derivation db)
  | rename (r : BoundCtx.Renaming β δ) :
      Equiv pureEff Γ da db → Equiv pureEff Γ (Typing.rename r da) (Typing.rename r db)
  | bsubst (s : Subst (Γ := Γ) β δ σ) (hs : ∀ i, Pure pureEff (σ i)) :
      Equiv pureEff Γ da db → Equiv pureEff Γ (Typing.bsubst s da) (Typing.bsubst s db)
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ} {a b : Tm ν Φ n}
      {da : Derivation Φ Γ β a (instrSrc f)} {db : Derivation Φ Γ β b (instrSrc f)} :
      Equiv pureEff Γ da db → Equiv pureEff Γ (.op (f := f) da) (.op db)
  | let₁ : Equiv pureEff Γ da da' → Equiv pureEff Γ db db' →
      Equiv pureEff Γ (.let₁ da db) (.let₁ da' db')
  | pair : Equiv pureEff Γ da da' → Equiv pureEff Γ db db' →
      Equiv pureEff Γ (.pair da db) (.pair da' db')
  | let₂ : Equiv pureEff Γ da da' → Equiv pureEff Γ db db' →
      Equiv pureEff Γ (.let₂ da db) (.let₂ da' db')
  | inl : Equiv pureEff Γ da db →
      Equiv pureEff Γ (.inl (h := hasCase) (B := B) da) (.inl db)
  | inr : Equiv pureEff Γ da db →
      Equiv pureEff Γ (.inr (h := hasCase) (A := A) da) (.inr db)
  | case : Equiv pureEff Γ de de' → Equiv pureEff Γ dl dl' → Equiv pureEff Γ dr dr' →
      Equiv pureEff Γ (.case (h := hasCase) de dl dr) (.case de' dl' dr')
  | abort : Equiv pureEff Γ da db →
      Equiv pureEff Γ (.abort (h := hasCase) (C := C) da) (.abort db)
  | iter : Equiv pureEff Γ da da' → Equiv pureEff Γ db db' →
      Equiv pureEff Γ (.iter (h := rfl) da db) (.iter da' db')
  | par : Equiv pureEff Γ da da' → Equiv pureEff Γ db db' →
      Equiv pureEff Γ (.par da db) (.par da' db')
  | swap (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) :
      Equiv pureEff Γ (Typing.swap (.par da db)) (.par db da)
  | assoc (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
      (dc : Derivation Φ Γ β c C) :
      Equiv pureEff Γ (Typing.assoc (.par (.par da db) dc)) (.par da (.par db dc))
  | purePair (ha : Pure pureEff a) (hb : Pure pureEff b)
      (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) :
      Equiv pureEff Γ (.par da db) (.pair da db)
  | unitLeft (da : Derivation Φ Γ β a A) :
      Equiv pureEff Γ (Typing.dropLeft (.par .unit da)) da
  | unitRight (da : Derivation Φ Γ β a A) :
      Equiv pureEff Γ (Typing.dropRight (.par da .unit)) da
  | map (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
      (df : Derivation Φ Γ (.snoc β A) f C) (dg : Derivation Φ Γ (.snoc β B) g D)
      (hf : Pure pureEff f) (hg : Pure pureEff g) :
      Equiv pureEff Γ (.par (.let₁ da df) (.let₁ db dg))
        (.let₂ (.par da db) (.pair (Typing.leftResult df) (Typing.underBinder dg)))
  | parCaseLeft (de : Derivation Φ Γ β e (coprod A B)) (he : Pure pureEff e)
      (dl : Derivation Φ Γ (.snoc β A) l C) (dr : Derivation Φ Γ (.snoc β B) r C)
      (dp : Derivation Φ Γ β p D) :
      Equiv pureEff Γ (.par (.case (h := hasCase) de dl dr) dp)
        (.case (h := hasCase) de (.par dl (Typing.lift dp)) (.par dr (Typing.lift dp)))
  | parCaseRight (de : Derivation Φ Γ β e (coprod A B)) (he : Pure pureEff e)
      (dl : Derivation Φ Γ (.snoc β A) l C) (dr : Derivation Φ Γ (.snoc β B) r C)
      (dp : Derivation Φ Γ β p D) :
      Equiv pureEff Γ (.par dp (.case (h := hasCase) de dl dr))
        (.case (h := hasCase) de (.par (Typing.lift dp) dl) (.par (Typing.lift dp) dr))
  | letBeta (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
      (ha : Pure pureEff a) :
      Equiv pureEff Γ (.let₁ da db) (Typing.instantiate db da)
  | letEta (da : Derivation Φ Γ β a A) :
      Equiv pureEff Γ (.let₁ da Typing.newest) da
  | iterFixpoint (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
      Equiv pureEff Γ (.iter (h := rfl) da db)
        (.let₁ da (.case (h := hasCase) db Typing.newest
          (.iter (h := rfl) Typing.newest (Typing.underBinder (Typing.underBinder db)))))
  /-- A pure state change whose feedback square is a generated equation. -/
  | iterUniformity (da : Derivation Φ Γ β a A)
      (dh : Derivation Φ Γ (.snoc β A) h A') (hp : Pure pureEff h)
      (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
      (db' : Derivation Φ Γ (.snoc β A') b' (coprod B A'))
      (square : Equiv pureEff Γ (Typing.uniformityLeft db dh) (Typing.uniformityRight db' dh)) :
      Equiv pureEff Γ (.iter (h := rfl) da db) (.iter (h := rfl) (.let₁ da dh) db')
  | iterBind (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
      Equiv pureEff Γ (.iter (h := rfl) da db)
        (.let₁ da (.iter (h := rfl) Typing.newest (Typing.underBinder db)))

end Silmaril.Isotope.LetParIter
