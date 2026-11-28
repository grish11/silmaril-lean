module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

open Silmaril.Elgot.ITree
open Isotope.Semantics (BoundEnv ProductModel UnitModel CoproductModel EmptyModel InstructionModel)
open LetCase.LocallyNameless (Derivation)
open LetCase (HandledTrace.Program HandledTrace.denote_rename)

universe u v e

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {M : InstructionModel D Φ (Tree Events)}
  {n : Nat} {β : BoundCtx τ n} {A X Y Z : τ}

local notation "⟪" d "⟫" => Derivation.denote D M d (fun x => Empty.elim x)

theorem denote_seq_proof {s : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (a : Derivation Φ Ctx.nil (β.snoc X) s Y) (b : Derivation Φ Ctx.nil (β.snoc Y) t Z)
    (ρ : BoundEnv D β) (x : D X) :
    ⟪Derivation.let₁ a b.underBinder⟫ (ρ.snoc x) = (⟪a⟫ (ρ.snoc x) >>= fun y => ⟪b⟫ (ρ.snoc y)) := by
  change (⟪a⟫ (ρ.snoc x) >>= fun y => ⟪b.underBinder⟫ ((ρ.snoc x).snoc y)) = _
  exact bind_congr fun y => HandledTrace.denote_rename b (BoundCtx.Renaming.underBinder β X Y) _ _
    (Fin.cases HEq.rfl (fun _ => HEq.rfl))

theorem denote_keep_proof (a : Operand Φ ((β.snoc A).snoc X) Y) (ρ : BoundEnv D β) (v : D A) (x : D X) :
    ⟪(keep a).2⟫ (ρ.snoc ((ProductModel.productEquiv A X).symm (v, x))) =
      (⟪a.2⟫ ((ρ.snoc v).snoc x) >>= fun y => pure ((ProductModel.productEquiv A Y).symm (v, y))) := by
  simp only [keep, Derivation.denote, BoundEnv.snoc_zero]
  erw [pure_bind, Equiv.apply_symm_apply, pure_bind]
  exact congrArg (· >>= _) (HandledTrace.denote_rename a.2 _ _ _
    (Fin.cases HEq.rfl (Fin.cases HEq.rfl (fun _ => HEq.rfl))))

omit [TypeFormers τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D] in
private theorem snoc_eta (ρ : BoundEnv D (β.snoc A)) :
    ∃ (older : BoundEnv D β) (v : D A), ρ = older.snoc v :=
  ⟨fun i => ρ i.succ, ρ 0, funext (Fin.cases rfl (fun _ => rfl))⟩

theorem run_pack_proof : ∀ {n : Nat} (β : BoundCtx τ n) {X Y : τ} (a : Operand Φ (β.snoc X) Y)
    (ρ : BoundEnv D β) (x : D X),
    (pack β a).run M (wrapValue β ρ x) = (⟪a.2⟫ (ρ.snoc x) >>= fun y => pure (wrapValue β ρ y))
  | _, .nil, _, _, a, ρ, x => by
    have env : ρ = fun i => i.elim0 := funext fun i => i.elim0
    subst env
    exact (bind_pure _).symm
  | _, .snoc β A, X, Y, a, ρ, x => by
    obtain ⟨older, v, rfl⟩ := snoc_eta ρ
    change (pack β (keep a)).run M (wrapValue β older ((ProductModel.productEquiv A X).symm (v, x))) =
      (⟪a.2⟫ ((older.snoc v).snoc x) >>= fun y =>
        pure (wrapValue β older ((ProductModel.productEquiv A Y).symm (v, y))))
    rw [run_pack_proof β (keep a), denote_keep_proof, bind_assoc]
    exact bind_congr fun y => pure_bind _ _

omit [UnitModel D] [CoproductModel D] [EmptyModel D] in
theorem wrapValue_surjective_proof : ∀ {n : Nat} (β : BoundCtx τ n) {X : τ} (w : D (wrap β X)),
    ∃ (ρ : BoundEnv D β) (x : D X), wrapValue β ρ x = w
  | _, .nil, _, w => ⟨fun i => i.elim0, w, rfl⟩
  | _, .snoc β A, X, w => by
    obtain ⟨ρ, packed, rfl⟩ := wrapValue_surjective_proof β (X := product A X) w
    obtain ⟨⟨v, x⟩, rfl⟩ := (ProductModel.productEquiv A X).symm.surjective packed
    exact ⟨ρ.snoc v, x, rfl⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled
