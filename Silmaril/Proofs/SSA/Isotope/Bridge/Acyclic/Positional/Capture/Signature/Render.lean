module
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Signature.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
open Morphism (SignatureMap)
open Institution (InstrSig)
open LetCase.LocallyNameless (Derivation)
open Reverse

set_option backward.isDefEq.respectTransparency false

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {d m : Nat} {β : BoundCtx τ d} {γ : BoundCtx τ m} {L : LCtx τ}

private theorem rename_transport {t : LetCase.LocallyNameless.Tm Empty Q.Instr d} {A B : υ}
    {β : BoundCtx υ d} {γ : BoundCtx υ m} (r : BoundCtx.Renaming β γ) (e : A = B)
    (a : Derivation Q.Instr .nil β t A) :
    (e ▸ a : Derivation Q.Instr .nil β t B).rename r =
      (e ▸ a.rename r : Derivation Q.Instr .nil γ (t.rename r.toFun) B) := by
  cases e
  rfl

private theorem map_transport {t : LetCase.LocallyNameless.Tm Empty P.Instr d} {A B : τ}
    (e : A = B) (a : Derivation P.Instr .nil β t A) :
    (e ▸ a : Derivation P.Instr .nil β t B).mapSignature g =
      (congrArg g.ty e ▸ a.mapSignature g :
        Derivation Q.Instr .nil (β.mapTypes g.ty) (t.mapInstr g.instr) (g.ty B)) := by
  cases e
  rfl

private theorem rename_map_aux {t : LetCase.LocallyNameless.Tm Empty P.Instr d} {A : τ}
    (a : Derivation P.Instr .nil β t A) (r : BoundCtx.Renaming β γ)
    (s : BoundCtx.Renaming (β.mapTypes g.ty) (γ.mapTypes g.ty)) (same : r.toFun = s.toFun) :
    HEq ((a.rename r).mapSignature g) ((a.mapSignature g).rename s) := by
  induction a generalizing m with
  | fv hi => cases hi
  | bv =>
    simp only [Derivation.rename, map_transport, Derivation.mapSignature, rename_transport]
    simp only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq]
    congr! (config := .unfoldSameFun) 1
    simp [← same]
  | op a ih =>
    have ha := ih r s same
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    simp only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq]
    congr! (config := .unfoldSameFun) 1
    · simp [← same]
    · simpa only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq] using ha
  | let₁ a b iha ihb =>
    have ha := iha r s same
    have hb := ihb (r.up _) (s.up _) (by simp [BoundCtx.Renaming.up, same])
    simp only [Derivation.rename, Derivation.mapSignature]
    congr! (config := .unfoldSameFun) 1 <;> simp [← same]
  | unit =>
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    rfl
  | pair a b iha ihb =>
    have ha := iha r s same
    have hb := ihb r s same
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    simp only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq]
    congr! (config := .unfoldSameFun) 1 <;> simp [← same]
  | let₂ a b iha ihb =>
    have ha := iha r s same
    have hb := ihb ((r.up _).up _) ((s.up _).up _) (by simp [BoundCtx.Renaming.up, same])
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    congr! (config := .unfoldSameFun) 1
    all_goals solve
      | simp [← same]
      | simpa only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq] using ha
  | inl a ih =>
    have ha := ih r s same
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    simp only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq]
    congr! (config := .unfoldSameFun) 1
    simp [← same]
  | inr a ih =>
    have ha := ih r s same
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    simp only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq]
    congr! (config := .unfoldSameFun) 1
    simp [← same]
  | case e l r ihe ihl ihr =>
    have he := ihe r s same
    have hl := ihl (r.up _) (s.up _) (by simp [BoundCtx.Renaming.up, same])
    have hr := ihr (r.up _) (s.up _) (by simp [BoundCtx.Renaming.up, same])
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    congr! (config := .unfoldSameFun) 1
    all_goals solve
      | simp [← same]
      | simpa only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq] using he
  | abort a ih =>
    have ha := ih r s same
    simp only [Derivation.rename, Derivation.mapSignature, rename_transport]
    congr! (config := .unfoldSameFun) 1
    · simp [← same]
    · simpa only [eqRec_eq_cast, cast_heq_iff_heq, heq_cast_iff_heq] using ha

omit [TypeFormers τ] [TypeFormers υ] in
private theorem Scope.renaming_mapTypes (f : τ → υ) (s : Scope β γ) :
    (s.mapTypes f).renaming.toFun = s.renaming.toFun := by
  induction s with
  | base => rfl
  | skip s A ih =>
    simp only [Scope.mapTypes, Scope.renaming, BoundCtx.Renaming.comp, BoundCtx.Renaming.succ, ih]

private theorem scope_operand_map (s : Scope β γ) {A B : τ}
    (a : Operand P.Instr (β.snoc A) B) :
    (s.operand a).mapSignature g = (s.mapTypes g.ty).operand (a.mapSignature g) := by
  have same : (s.renaming.up A).toFun = ((s.mapTypes g.ty).renaming.up (g.ty A)).toFun := by
    simp [BoundCtx.Renaming.up, Scope.renaming_mapTypes]
  apply Sigma.ext
  · exact (LetCase.LocallyNameless.Tm.mapInstr_rename _ _ _).trans (congrArg
      (fun f => (a.1.mapInstr g.instr).rename f) same)
  · exact rename_map_aux g a.2 _ _ same

private theorem scope_operand_cast {β : BoundCtx υ d} {γ : BoundCtx υ m}
    (s : Scope β γ) {A B D : υ} (a : Operand Q.Instr (β.snoc A) B) (e : B = D) :
    s.operand (a.castResult e) = (s.operand a).castResult e := by
  cases e
  rfl

mutual

private theorem tree_render_map : ∀ {A : τ} (t : Tree P.Instr β L A)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
    ((t.mapSignature g).render (s.mapTypes g.ty)) = (t.render s).mapSignature g
  | A, .jump a k, _, _, s => by
    simp only [Tree.mapSignature, Tree.render, FiniteExit.mapSignature, Code.mapSignature]
    rw [scope_operand_map, ← Scope.mapTypes, edge_render_map k (s.skip A)]
  | A, .case a l r, _, _, s => by
    simp only [Tree.mapSignature, Tree.render, FiniteExit.mapSignature, scope_operand_cast]
    rw [scope_operand_map, ← Scope.mapTypes, edge_render_map l (s.skip A), edge_render_map r (s.skip A)]
termination_by structural _ t => t

private theorem edge_render_map : ∀ {A : τ} (k : Edge P.Instr β L A)
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
    ((k.mapSignature g).render (s.mapTypes g.ty)) = (k.render s).mapSignature g
  | _, .exit _, _, _, _ => rfl
  | _, .local t, _, _, s => tree_render_map t s
termination_by structural _ k => k

end

theorem program_render_map (p : Program P.Instr β L) :
    (p.mapSignature g).toFiniteExit = p.toFiniteExit.mapSignature g := by
  simp only [Program.mapSignature, Program.toFiniteExit, FiniteExit.mapSignature, Code.mapSignature]
  exact congrArg (FiniteExit.join (.br (p.entry.mapSignature g))) (tree_render_map g p.body .base)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
