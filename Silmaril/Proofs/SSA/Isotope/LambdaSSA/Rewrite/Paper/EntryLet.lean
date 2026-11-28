module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

/-! # Arity boundary of literal CFG η and codiagonal -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLet

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem of_entryEta {n : Nat} (h : Paper.EntryEta τ Φ n) :
    CfgEta.EntryLet (Paper.Eqv (τ := τ) (Φ := Φ)) n := by
  intro Γ L S a d blocks R ha hd hb
  have before := h R (.let₁ ha hd) hb
  change Paper.Eqv Γ (.cfg (.let₁ a d) n blocks)
    (.let₁ a (d.lsubst (liftLSubstVars (cfgEntryContinuations blocks)))) L at before
  rw [lift_cfgEntryContinuations] at before
  exact before.trans (.let₁ ha (h R hd
    (fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i)))).symm)

theorem flattened_lsubst_ne_flat {n : Nat} (hn : n ≠ 1)
    (entry body : Region Φ) (σ : Nat → Region Φ) (e : Region Φ) (blocks : Fin n → Region Φ) :
    ((CfgEta.Codiagonal.flattened entry body).lsubst σ) ≠ .cfg e n blocks := by
  intro eq
  let arity : Region Φ → Nat
    | .cfg _ k _ => k
    | _ => 0
  exact hn (congrArg arity eq).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLet
