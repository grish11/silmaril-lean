module

public import Silmaril.Logic.Algebraic.Lambda.Institution

/-! Public intrinsically typed lambda terms and full-function set models, with
arbitrary base-type maps. Sentences are equations only: raw typing reflection
cannot admit maps that identify distinct source base types. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCEquations
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Silmaril.Calculi.LambdaCube.STLC
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- A separate signature category on the actual public lambda signatures. -/
structure Language where
  source : Signature

/-- Base types and symbols may be identified; each operator profile is mapped exactly. -/
structure Hom (S T : Language) where
  base : S.source.Base → T.source.Base
  op : ∀ {as τ}, S.source.Op as τ →
    T.source.Op (as.map (mapTy base)) (mapTy base τ)

/-- Identity signature translation. -/
def Hom.identity (S : Language) : Hom S S where
  base := id
  op := by
    intro as τ o
    simpa only [mapTy_id, List.map_id, id_eq] using o

/-- Composition of signature translations. -/
def Hom.comp {S T U : Language} (f : Hom S T) (g : Hom T U) : Hom S U where
  base := g.base ∘ f.base
  op := by
    intro as τ o
    simpa only [mapTy_comp, List.map_map, Function.comp_apply] using g.op (f.op o)

/-- Base maps and the dependent operator maps determine a signature map. -/
theorem Hom.ext {S T : Language} {f g : Hom S T}
    (hb : f.base = g.base) (ho : HEq (@f.op) (@g.op)) : f = g := by
  cases f
  cases g
  cases hb
  cases ho
  rfl

/-- Operator translation respects transport of its dependent indices. -/
theorem Hom.op_heq {S T : Language} (f : Hom S T)
    {as bs : List (Ty S.source.Base)} {τ υ : Ty S.source.Base}
    (ha : as = bs) (ht : τ = υ) {o : S.source.Op as τ} {p : S.source.Op bs υ}
    (ho : HEq o p) : HEq (f.op o) (f.op p) := by
  subst bs
  subst υ
  cases ho
  rfl

/-- Intrinsic signature translation, including changes of base types. -/
def mapTerm {S T : Language} (f : Hom S T) :
    {Γ : Ctx S.source.Base} → {τ : Ty S.source.Base} → Term S.source Γ τ →
      Term T.source (Γ.map (mapTy f.base)) (mapTy f.base τ)
  | _, _, .var x => .var (x.map (mapTy f.base))
  | _, _, .lam t => .lam (mapTerm f t)
  | _, _, .app t u => .app (mapTerm f t) (mapTerm f u)
  | _, _, .op o args => .op (f.op o)
      (reindexTuple (mapTy f.base) (fun _ x => mapTerm f (args _ x)))

/-- Models move backwards by restricting base carriers and operators. -/
def reduct {S T : Language} (f : Hom S T) (M : SetModel T.source) : SetModel S.source where
  base := M.base ∘ f.base
  op o args := (carrierMap f.base M.base _).symm (M.op (f.op o) (envMap f.base M.base args))

/-- An equation retains its actual typed context and result type. -/
inductive Sentence (S : Language) where
  | equation {Γ : Ctx S.source.Base} {τ : Ty S.source.Base}
      (lhs rhs : Term S.source Γ τ)

def mapSentence {S T : Language} (f : Hom S T) : Sentence S → Sentence T
  | .equation t u => .equation (mapTerm f t) (mapTerm f u)

/-- Equality holds at every assignment, including function-valued variables. -/
def Holds {S : Language} (M : SetModel S.source) : Sentence S → Prop
  | .equation t u => ∀ ρ, eval M t ρ = eval M u ρ

def toPublicSentence {S : Language} : Sentence S → STLC.Sentence S.source
  | .equation t u => .equation t u

theorem holds_public {S : Language} (M : SetModel S.source) (p : Sentence S) :
    Holds M p ↔ STLC.Sat M (toPublicSentence p) := by cases p; rfl

/-- Composition acts by ordinary composition on base types. -/
@[simp] theorem Hom.comp_base {S T U : Language} (f : Hom S T) (g : Hom T U) :
    (f.comp g).base = g.base ∘ f.base := rfl

/-- The composite operator map agrees with successive translation up to transport. -/
@[simp] theorem Hom.comp_op {S T U : Language} (f : Hom S T) (g : Hom T U)
    {as τ} (o : S.source.Op as τ) : HEq ((f.comp g).op o) (g.op (f.op o)) := by
  simp [Hom.comp]

/-- Every public full-function set model remains, with small equality arrows. -/
abbrev Model (S : Language) := Algebraic.Lambda.LambdaModel S.source

def pullModel {S T : Language} (f : Hom S T) (M : Model T) : Model S :=
  ⟨reduct f M.toSetModel⟩

def reductFunctor {S T : Language} (f : Hom S T) : Model T ⥤ Model S where
  obj := pullModel f
  map h := ⟨congrArg (pullModel f) h.down⟩


end Silmaril.Logic.STLCEquations
