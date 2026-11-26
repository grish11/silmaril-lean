module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.CFG.Lexical.Thms
import Silmaril.SSA.LambdaRTL.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

variable {V F F' F'' α : Type} {a b c : Nat}

private theorem term_mapOp_relabel {K K' : Type} (h : F → F') (rename : K → K')
    (term : Term V K F) : (term.relabel rename).mapOp h = (term.mapOp h).relabel rename := by
  induction term <;> simp_all [Term.relabel, Term.mapOp]

private theorem body_mapOp_relabel {K K' : Type} (h : F → F') (rename : K → K')
    (body : Body V K F) : (body.relabel rename).mapOp h = (body.mapOp h).relabel rename := by
  induction body <;> simp_all [Body.relabel, Body.mapOp, term_mapOp_relabel]

variable [DecidableEq V]

theorem mapOp_id (graph : Graph V F a b) : graph.mapOp id = graph := by
  cases graph
  simp only [Graph.mapOp, Block.mapOp, Body.mapOp_id]

theorem mapOp_comp (h : F → F') (k : F' → F'') (graph : Graph V F a b) :
    graph.mapOp (k ∘ h) = (graph.mapOp h).mapOp k := by
  cases graph
  simp only [Graph.mapOp, Block.mapOp, Body.mapOp_comp]

theorem mapOp_identity (h : F → F') (a : Nat) :
    (Graph.identity (V := V) (F := F) a).mapOp h = Graph.identity a := by
  unfold Graph.identity Graph.mapOp
  congr 1
  funext index
  exact Fin.elim0 index

theorem mapOp_link [Inhabited V] (h : F → F') (left : Graph V F a b) (right : Graph V F b c) :
    (left.link right).mapOp h = (left.mapOp h).link (right.mapOp h) := by
  unfold Graph.mapOp Graph.link
  congr 1
  funext index
  refine Fin.addCases (fun addr => ?_) (fun addr => ?_) index
  · refine Fin.addCases (fun i => ?_) (fun port => ?_) addr
    · simp [Graph.linkedBlock, Block.mapOp, Block.relabel, body_mapOp_relabel, Graph.leftLabel]
      rfl
    · simp [Graph.linkedBlock, Graph.handoff, Block.mapOp, Body.mapOp, Term.mapOp, Graph.rightLabel]
  · simp [Graph.linkedBlock, Block.mapOp, Block.relabel, body_mapOp_relabel, Graph.rightLabel]

theorem denote_mapOp (h : F → F') (model : Model F' Part α) (graph : Graph V F a b) (input : Fin a × α) :
    (graph.mapOp h).denote model input = graph.denote (model.reduct h) input := by
  have step : (graph.mapOp h).step model = graph.step (model.reduct h) := by
    funext transfer
    rcases transfer with ⟨index | port, packet⟩
    · simp only [Graph.step, Graph.mapOp, Block.mapOp, Body.evalJump_eq_evalSSA,
        Body.toRegion_mapOp, Region.evalSSA_mapOp]
      rfl
    · rfl
  unfold Graph.denote
  rw [step]
  rfl

theorem namedRTL_mapOp [Inhabited V] (h : F → F') (graph : Graph V F a b) (port : Fin a) :
    (graph.mapOp h).namedRTL port = (graph.namedRTL port).mapOp h := by
  simp only [Graph.namedRTL, CFG.relabel, Graph.toCFG, Graph.mapOp, Graph.table, CFG.mapOp,
    Block.mapOp, Block.relabel, Body.mapOp, Term.mapOp, List.map_map, Function.comp_def,
    body_mapOp_relabel]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Institution
