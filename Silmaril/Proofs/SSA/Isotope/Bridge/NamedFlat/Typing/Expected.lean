module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Expected.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open LetCase.LocallyNameless (Tm HasType)

universe u v
variable {Base : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

private theorem inferAt_sound {n : Nat} (ctx : BoundCtx (Ty Base) n) (expr : Tm Empty F n)
    {expected : Option (Ty Base)} {A : Ty Base} (inferred : inferAt ctx expected expr = some A) :
    HasType F .nil ctx expr A := by
  induction expr generalizing expected A with
  | fv x => nomatch x
  | bv => cases inferred; exact .bv
  | unit => cases inferred; exact .unit
  | pair a b ihA ihB =>
    simp only [inferAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at inferred
    obtain ⟨_, ha, _, hb, rfl⟩ := inferred
    exact .pair (ihA ctx ha) (ihB ctx hb)
  | op f a ih =>
    by_cases typed : inferAt ctx (some (instrSrc f)) a = some (instrSrc f)
    · have eq : instrTrg f = A := by simpa [inferAt, typed] using inferred
      rw [← eq]
      exact .op (ih ctx typed)
    · simp [inferAt, typed] at inferred
  | let₁ value body ihValue ihBody =>
    simp only [inferAt, Option.bind_eq_some_iff] at inferred
    obtain ⟨B, valueType, bodyType⟩ := inferred
    exact .let₁ (ihValue ctx valueType) (ihBody (.snoc ctx B) bodyType)
  | let₂ value body ihValue ihBody =>
    cases valueType : inferAt ctx none value with
    | none => simp [inferAt, valueType] at inferred
    | some product =>
      cases product <;> simp only [inferAt, valueType] at inferred
      case product B C => exact .let₂ (ihValue ctx valueType) (ihBody (.snoc (.snoc ctx B) C) inferred)
      all_goals cases inferred
  | inl value ih =>
    cases expected with
    | none => cases inferred
    | some ty =>
      cases ty <;> simp only [inferAt] at inferred
      case coprod left right =>
        split at inferred
        · cases inferred
          exact .inl (ih ctx (by assumption))
        · cases inferred
      all_goals cases inferred
  | inr value ih =>
    cases expected with
    | none => cases inferred
    | some ty =>
      cases ty <;> simp only [inferAt] at inferred
      case coprod left right =>
        split at inferred
        · cases inferred
          exact .inr (ih ctx (by assumption))
        · cases inferred
      all_goals cases inferred
  | case test left right ihTest ihLeft ihRight =>
    cases checked : inferAt ctx none test with
    | none => simp [inferAt, checked] at inferred
    | some ty =>
      cases ty <;> simp only [inferAt, checked] at inferred
      case coprod a b =>
        change ((inferAt (.snoc ctx a) expected left).bind fun c =>
          if inferAt (.snoc ctx b) expected right = some c ∧ expected.getD c = c then some c else none) = some A at inferred
        obtain ⟨c, arm, next⟩ := Option.bind_eq_some_iff.mp inferred
        split at next
        · rename_i rightTyped
          cases next
          exact .case (ihTest ctx checked) (ihLeft (.snoc ctx a) arm) (ihRight (.snoc ctx b) rightTyped.1)
        · cases next
      all_goals cases inferred
  | abort => cases inferred

private theorem inferExpected_sound {n : Nat} (ctx : BoundCtx (Ty Base) n) (expr : Tm Empty F n)
    {A : Ty Base} (inferred : inferExpected ctx expr = some A) :
    HasType F .nil ctx expr A :=
  inferAt_sound ctx expr inferred

theorem checkBodyExpected_sound {labels n : Nat} (types : Fin labels → Ty Base)
    (ctx : BoundCtx (Ty Base) n) (body : LambdaSSA.Flat F labels n)
    (accepted : checkBodyExpected types ctx body = true) :
    LambdaSSA.Flat.HasType types ctx body := by
  induction body with
  | br label arg =>
    exact .br (inferAt_sound ctx arg (of_decide_eq_true accepted))
  | let₁ op rest ih =>
    cases inferred : inferExpected ctx op with
    | none => simp [checkBodyExpected, inferred] at accepted
    | some A =>
      exact .let₁ (inferExpected_sound ctx op inferred) (ih _ (by simpa [checkBodyExpected, inferred] using accepted))
  | let₂ op rest ih =>
    cases inferred : inferExpected ctx op with
    | none => simp [checkBodyExpected, inferred] at accepted
    | some A =>
      cases A <;> simp only [checkBodyExpected, inferred, Bool.false_eq_true] at accepted
      case product A B => exact .let₂ (inferExpected_sound ctx op inferred) (ih _ accepted)
  | case op left right ihLeft ihRight =>
    cases inferred : inferExpected ctx op with
    | none => simp [checkBodyExpected, inferred] at accepted
    | some A =>
      cases A <;> simp only [checkBodyExpected, inferred, Bool.false_eq_true, Bool.and_eq_true] at accepted
      case coprod A B =>
        exact .case (inferExpected_sound ctx op inferred) (ihLeft _ accepted.1) (ihRight _ accepted.2)

theorem checkExpected_sound {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) (accepted : checkExpected graph captures internal external = true) :
    graph.HasType captures internal external := by
  simp only [checkExpected, Bool.and_eq_true, List.all_eq_true] at accepted
  exact ⟨checkBodyExpected_sound _ _ _ accepted.1, fun i => checkBodyExpected_sound _ _ _ (accepted.2 i (by simp))⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
