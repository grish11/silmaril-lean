module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.TwoRequests.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests
open Morphism.CaseSSA (erase)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer term term_tree_of_agree)
open Silmaril.Elgot.ITree (Tree iterate_fixpoint)
open Silmaril.Elgot (iter)

universe u w
variable {E : Type w → Type w} {F : Type} {α : Type u} {exits captures : Nat}
  {source : FiniteCFG F 1 exits captures}
  (instr : Primitive E F α) (env : Env α) (s : Shape source) (emitted : Emitted s)

private noncomputable def step {blocks : Nat} (graph : FiniteCFG F blocks exits captures) (p : BlockInput α blocks) :
    Tree E (Transfer α ⊕ BlockInput α blocks) :=
  region instr (extend env p.2) (graph.block p.1).erase >>= fun out => pure (splitTransfer blocks out)

private theorem entry_run {blocks : Nat} (graph : FiniteCFG F blocks exits captures)
    (positive : 0 < blocks) (entry : graph.entry.erase = .br 0 s.seed) :
    region instr env graph.erase =
      term instr env s.seed >>= fun packet => iter (step instr env graph) (⟨0, positive⟩, packet) := by
  simp only [FiniteCFG.erase, region, entry, bind_assoc, pure_bind, splitTransfer, positive, dite_eq_left,
    Sum.elim_inr]
  rfl

private theorem exit_transfer (blocks : Nat) (value : Value α) :
    splitTransfer blocks (blocks + s.exit.val, value) = .inl (s.exit.val, value) := by
  simp [splitTransfer, show ¬ blocks + s.exit.val < blocks by omega]

private theorem original_packet (packet : Value α) :
    iter (step instr env source) (0, packet) =
      term instr (extend env packet) (.op s.first (erase s.arg₁)) >>= fun first =>
        term instr (extend (extend env packet) first) (.op s.second (erase s.arg₂)) >>= fun second =>
          term instr (extend (extend (extend env packet) first) second) (erase s.result) >>= fun output =>
            pure (s.exit.val, output) := by
  rw [congrFun (iterate_fixpoint (step instr env source)) (0, packet)]
  simp [step, s.row_eq, region, bind_assoc, exit_transfer s]

private theorem continuation_packet (packet first : Value α) :
    iter (step instr env emitted.code) (1, .pair packet first) =
      term instr (extend (extend env packet) first) (.op s.second (erase s.arg₂)) >>= fun second =>
        term instr (extend (extend (extend env packet) first) second) (erase s.result) >>= fun output =>
          pure (s.exit.val, output) := by
  let old := extend (extend env packet) first
  let extra := extend (extend (extend env (.pair packet first)) packet) first
  have arg : term instr extra (erase s.arg₂) = term instr old (erase s.arg₂) :=
    term_tree_of_agree instr _ (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  have result (second : Value α) :
      term instr (extend extra second) (erase s.result) =
        term instr (extend old second) (erase s.result) :=
    term_tree_of_agree instr _ (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))))
  rw [congrFun (iterate_fixpoint (step instr env emitted.code)) (1, .pair packet first)]
  simp only [step, emitted.second_eq, secondRow, region, term, bind_assoc, pure_bind,
    show extend env (.pair packet first) 0 = .pair packet first from rfl,
    exit_transfer s, Sum.elim_inl]
  change (term instr extra (erase s.arg₂) >>= fun value => instr s.second value >>= fun second =>
    term instr (extend extra second) (erase s.result) >>= fun output => pure (s.exit.val, output)) = _
  simp only [arg, result, old]

theorem preserves_run : region instr env source.erase = region instr env emitted.code.erase := by
  rw [entry_run instr env s source (by decide) s.entry_eq,
    entry_run instr env s emitted.code (by decide) (emitted.entry_eq.trans s.entry_eq)]
  apply bind_congr
  intro packet
  change iter (step instr env source) (0, packet) = iter (step instr env emitted.code) (0, packet)
  rw [original_packet instr env s, congrFun (iterate_fixpoint (step instr env emitted.code)) (0, packet)]
  simp only [step, emitted.first_eq, firstRow, region, bind_assoc, term, pure_bind]
  change _ = term instr (extend env packet) (erase s.arg₁) >>= fun value =>
    instr s.first value >>= fun first => iter (step instr env emitted.code) (1, .pair packet first)
  simp only [continuation_packet instr env s emitted, term, bind_assoc]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.TwoRequests
