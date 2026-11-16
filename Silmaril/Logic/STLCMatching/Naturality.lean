module

public import Silmaril.Logic.STLCMatching.Signatures

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCMatching
open CategoryTheory Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc
variable {B : Type} {S T : FixedSignature B}

def Comb.map (f : S ⟶ T) : {Γ : Ctx S.source.Base} → {τ : Ty S.source.Base} →
    Comb S.source Γ τ → Comb T.source Γ τ
  | _, _, .var v => .var v
  | _, _, .primitive p => .primitive (FixedHom.primitive f p)
  | _, _, .app t u => .app (t.map f) (u.map f)

theorem Comb.map_app (f : S ⟶ T) {Γ : Ctx S.source.Base} {a b : Ty S.source.Base}
    (t : Comb S.source Γ (.arrow a b)) (u : Comb S.source Γ a) :
    (t.app u).map f = (t.map f).app (u.map f) := by
  cases b <;> simp [Comb.map]

theorem Comb.map_abstract (f : S ⟶ T) {Γ : Ctx S.source.Base} {a b : Ty S.source.Base}
    (t : Comb S.source (a :: Γ) b) : t.abstract.map f = (t.map f).abstract := by
  induction t with
  | var v =>
      cases v with
      | zero =>
          simp only [Comb.abstract.eq_1 (S := S.source), Comb.abstract.eq_1 (S := T.source),
            Comb.map.eq_1 (S := S) (T := T), Comb.map.eq_2 (S := S) (T := T), FixedHom.primitive]
      | succ v =>
          simp only [Comb.abstract.eq_2 (S := S.source), Comb.abstract.eq_2 (S := T.source),
            Comb.map.eq_1 (S := S) (T := T), Comb.map.eq_2 (S := S) (T := T),
            Comb.map.eq_3 (S := S) (T := T), FixedHom.primitive]
  | primitive p => simp [Comb.abstract, Comb.map, FixedHom.primitive]
  | app t u iht ihu => simp [Comb.abstract, Comb.map, FixedHom.primitive, iht, ihu]

theorem Comb.map_applyArgs (f : S ⟶ T) {Γ : Ctx S.source.Base} {τ : Ty S.source.Base}
    {as : List (Ty S.source.Base)} (t : Comb S.source Γ (curryTy as τ))
    (args : Tuple (Comb S.source Γ) as) :
    (t.applyArgs args).map f = (t.map f).applyArgs (fun _ x => (args _ x).map f) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [Comb.applyArgs.eq_2]
      have hmap := Comb.map_app f t (args _ .zero)
      exact (ih (.app t (args _ .zero)) (fun _ x => args _ (.succ x))).trans
        (congrArg (fun q => q.applyArgs (fun _ x => (args _ (.succ x)).map f)) hmap)

theorem compile_mapOp (f : S ⟶ T) {Γ : Ctx S.source.Base} {τ : Ty S.source.Base} (t : Term S.source Γ τ) :
    compile (t.mapOp f.operators) = (compile t).map f := by
  induction t with
  | var v => simp only [Term.mapOp, compile.eq_1, Comb.map.eq_1]
  | lam t ih => simp only [Term.mapOp, compile, ih, Comb.map_abstract]
  | app t u iht ihu => simp only [Term.mapOp, compile, Comb.map, iht, ihu]
  | op o args ih => simp only [Term.mapOp, compile, Comb.map_applyArgs, Comb.map,
      FixedHom.primitive, ih]

theorem Comb.pattern_map (f : S ⟶ T) {Γ : Ctx S.source.Base} {k : Nat}
    {Δ : Fin k → Ty S.source.Base}
    (vars : Tuple (Matching.FirstOrder.Pattern (nativeSignature S.source).symbols Δ) Γ)
    {τ : Ty S.source.Base} (t : Comb S.source Γ τ) :
    Matching.FirstOrder.Pattern.map (FixedHom.native (S := S) (T := T) f) (t.pattern vars) =
      (t.map f).pattern (fun a v => Matching.FirstOrder.Pattern.map (FixedHom.native (S := S) (T := T) f) (vars a v)) := by
  induction t with
  | var v => simp only [Comb.pattern.eq_1, Comb.map.eq_1]
  | primitive p =>
      simp only [Comb.pattern, Comb.map, Matching.FirstOrder.Pattern.map, FixedHom.native]
      congr 1
      funext i
      exact i.elim0
  | app t u iht ihu =>
      simp only [Comb.pattern, Comb.map, nativeApp, Matching.FirstOrder.Pattern.map,
        FixedHom.native]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => z.elim0) j) i
      · exact iht
      · exact ihu

theorem nativeVars_map (f : S ⟶ T) (Γ : Ctx B) :
    (fun a v => Matching.FirstOrder.Pattern.map (FixedHom.native (S := S) (T := T) f) (nativeVars Γ a v)) =
      (nativeVars (S := T.source) Γ : Tuple (Matching.FirstOrder.Pattern (nativeSignature T.source).symbols Γ.get) Γ) := by
  apply (Tuple.equivFn Γ).injective
  funext i
  change Matching.FirstOrder.Pattern.map (FixedHom.native (S := S) (T := T) f)
    (nativeVars (S := S.source) Γ _ (Var.ofFin i)) = nativeVars (S := T.source) Γ _ (Var.ofFin i)
  unfold nativeVars
  rw [Tuple.ofFn_ofFin, Tuple.ofFn_ofFin]
  rfl

theorem termPattern_map (f : S ⟶ T) {Γ : Ctx S.source.Base} {τ : Ty S.source.Base} (t : Term S.source Γ τ) :
    Matching.FirstOrder.Pattern.map (FixedHom.native (S := S) (T := T) f) (termPattern t) =
      termPattern (t.mapOp f.operators) := by
  unfold termPattern
  rw [Comb.pattern_map, nativeVars_map (S := S) (T := T) f Γ,
    compile_mapOp (S := S) (T := T) f t]

end Silmaril.Logic.STLCMatching
