module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open LetCase.LocallyNameless (Tm HasType)

universe u v
variable {Base : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

private theorem infer_sound {n : Nat} (ctx : BoundCtx (Ty Base) n) (expr : Tm Empty F n)
    {A : Ty Base} (inferred : infer ctx expr = some A) :
    HasType F .nil ctx expr A := by
  induction expr generalizing A with
  | fv x => nomatch x
  | bv => cases inferred; exact .bv
  | unit => cases inferred; exact .unit
  | pair a b ihA ihB =>
    simp only [infer, Option.bind_eq_some_iff, Option.map_eq_some_iff] at inferred
    obtain ⟨_, ha, _, hb, rfl⟩ := inferred
    exact .pair (ihA ctx ha) (ihB ctx hb)
  | op f a ih =>
    by_cases typed : infer ctx a = some (instrSrc f)
    · have eq : instrTrg f = A := by simpa [infer, typed] using inferred
      rw [← eq]
      exact .op (ih ctx typed)
    · simp [infer, typed] at inferred
  | let₁ | let₂ | inl | inr | case | abort => cases inferred

private theorem checkBody_sound {labels n : Nat} (types : Fin labels → Ty Base)
    (ctx : BoundCtx (Ty Base) n) (body : LambdaSSA.Flat F labels n)
    (accepted : checkBody types ctx body = true) :
    LambdaSSA.Flat.HasType types ctx body := by
  induction body with
  | br label arg =>
    exact .br (infer_sound ctx arg (of_decide_eq_true accepted))
  | let₁ op rest ih =>
    cases inferred : infer ctx op with
    | none => simp [checkBody, inferred] at accepted
    | some A =>
      exact .let₁ (infer_sound ctx op inferred) (ih _ (by simpa [checkBody, inferred] using accepted))
  | let₂ op rest ih =>
    cases inferred : infer ctx op with
    | none => simp [checkBody, inferred] at accepted
    | some A =>
      cases A <;> simp only [checkBody, inferred, Bool.false_eq_true] at accepted
      case product A B => exact .let₂ (infer_sound ctx op inferred) (ih _ accepted)
  | case op left right ihLeft ihRight =>
    cases inferred : infer ctx op with
    | none => simp [checkBody, inferred] at accepted
    | some A =>
      cases A <;> simp only [checkBody, inferred, Bool.false_eq_true, Bool.and_eq_true] at accepted
      case coprod A B =>
        exact .case (infer_sound ctx op inferred) (ihLeft _ accepted.1) (ihRight _ accepted.2)

theorem check_sound {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) (accepted : check graph captures internal external = true) :
    graph.HasType captures internal external := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at accepted
  exact ⟨checkBody_sound _ _ _ accepted.1, fun i => checkBody_sound _ _ _ (accepted.2 i (by simp))⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
