module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
public import Silmaril.Semantics.ITree.Signature.Execution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction

open CategoryTheory
open Silmaril.Elgot.ITree (Signature)
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction

universe u v w
variable {S T : Signature.{u}} {Φ : Type v} {α : Type w}
  (f : S ⟶ T) (instr : Primitive S.Event Φ α)

private theorem term_reindex (env : Env α) (a : Tm Φ) :
    f.tree id (term instr env a) = term (fun op arg => f.tree id (instr op arg)) env a := by
  induction a generalizing env with
  | var | unit => exact f.tree_ret id _
  | op | pair | let₁ | inl | inr | abort => simp only [term, f.tree_bind, f.tree_pure, f.tree_diverge, *]
  | let₂ a b iha ihb =>
    simp only [term, f.tree_bind, iha]
    congr 1
    funext val
    cases val <;> simp [ihb, f.tree_diverge]
  | case a l r iha ihl ihr =>
    simp only [term, f.tree_bind, iha]
    congr 1
    funext val
    cases val <;> simp [ihl, ihr, f.tree_diverge]

theorem region_reindex (env : Env α) (r : Region Φ) :
    f.tree id (region instr env r) = region (fun op arg => f.tree id (instr op arg)) env r := by
  induction r generalizing env with
  | br | let₁ => simp only [region, f.tree_bind, f.tree_pure, term_reindex f instr, *]
  | let₂ a b ih =>
    simp only [region, f.tree_bind, term_reindex f instr]
    congr 1
    funext val
    cases val <;> simp [ih, f.tree_diverge]
  | case a l r ihl ihr =>
    simp only [region, f.tree_bind, term_reindex f instr]
    congr 1
    funext val
    cases val <;> simp [ihl, ihr, f.tree_diverge]
  | cfg e arity blocks ihe ihb =>
    simp only [region, f.tree_bind, ihe]
    congr 1
    funext out
    cases splitTransfer arity out with
    | inl => exact f.tree_ret id _
    | inr next =>
      let source (p : BlockInput α arity) :=
        region instr (extend env p.2) (blocks p.1) >>= fun out => pure (splitTransfer arity out)
      let target (p : BlockInput α arity) :=
        region (fun op arg => f.tree id (instr op arg)) (extend env p.2) (blocks p.1) >>=
          fun out => pure (splitTransfer arity out)
      change f.tree id (Silmaril.Elgot.iter source next) = Silmaril.Elgot.iter target next
      rw [f.tree_iter]
      congr 1
      funext p
      simp only [source, target, f.tree_bind, ihb, f.tree_pure]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction
