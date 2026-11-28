module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Prepare
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Restore
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty ValueSort dataPorts sortValue)
open GVN.Cyclic
open GVN.Cyclic.Activation (Inputs inputSlot)
open GVN.Cyclic.Builder (Built Vertex build?)
open GVN.Cyclic.Builder.Preheader
open GVN.Cyclic.Deletion (DeletedLoop)
open Pure.SubZero (Opcode model)
open Silmaril.SSA.RVSDG (Port)
open scoped Pure.WordNormalize

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit} {loop : Native inputs carried entrySigs headerSigs out}
variable {result : DeletedLoop Opcode inputs carried entrySigs out}

private theorem entryWires_direct (lanes : List (ValueSort Unit))
    (lift : ∀ {s}, Port lanes s → Port carried s)
    {s : ValueSort Unit} (p : Port (dataPorts lanes) (.value s)) :
    ∃ entry : Port (carried ++ inputs) s,
      (entryWires loop (number loop) lanes lift).get p = .arg (inputSlot entry) := by
  induction lanes with
  | nil => cases p
  | cons _ _ ih =>
    cases p with
    | head => exact ⟨frontPort (canonicalLane loop (number loop) (lift .head)), rfl⟩
    | tail inner => exact ih (fun port => lift (.tail port)) inner

theorem prepare_builds (loop : Native inputs carried entrySigs headerSigs out) :
    ∃ built, build? (prepare loop) = some built :=
  GVN.Cyclic.Builder.build_of_direct_entry (entryWires_direct (loop := loop) carried (fun port => port))

theorem optimize_witness (accepted : optimize? loop = some result) :
    ∃ built : Built (prepare loop), ∃ edited, build? (prepare loop) = some built ∧
      Pass.step? built.view = some edited ∧ restore? loop edited = some result := by
  obtain ⟨built, builtEq, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨edited, editedEq, restored⟩ := Option.bind_eq_some_iff.mp next
  exact ⟨built, edited, builtEq, editedEq, restored⟩

theorem optimize_entry (accepted : optimize? loop = some result) :
    result.graph.preheader = loop.preheader ∧ result.graph.phiInputs .entry = loop.phiInputs .entry :=
  let ⟨_, _, _, _, restored⟩ := optimize_witness accepted
  ⟨(restore_entry restored).1, (restore_entry restored).2.1⟩

theorem optimize_count (accepted : optimize? loop = some result) :
    result.headerSigs.length + 1 = headerSigs.length := by
  obtain ⟨built, _, _, stepped, restored⟩ := optimize_witness accepted
  rw [(restore_entry restored).2.2]
  exact Pass.step_count built.view stepped

theorem initial_agrees (built : Built (prepare loop)) (input : Inputs model inputs) :
    built.view.LatchesAgree (FixedPoint.normalize built.graph) model
      (loop.initial model input) (loop.initial model input) := by
  have agrees := built.initial_agrees (m := model) (input₁ := preparedInput loop input)
    (input₂ := preparedInput loop input) (fun _ => rfl)
  simpa only [prepare_initial input] using agrees

theorem optimize_activation (accepted : optimize? loop = some result) {built : Built (prepare loop)}
    (builtEq : build? (prepare loop) = some built)
    (input : Inputs model inputs) (old : Inputs model carried)
    (invariant : built.view.LatchesAgree (FixedPoint.normalize built.graph) model old old) :
    result.graph.step model input old = loop.step model input old := by
  obtain ⟨actual, _, builtActual, stepped, restored⟩ := optimize_witness accepted
  have same := Option.some.inj (builtActual.symm.trans builtEq)
  subst actual
  exact (restore_step restored input old).trans
    ((Pass.step_activation built.view stepped model (preparedInput loop input) old invariant).trans (prepare_step input old))

private theorem evalFrom_eq {left right : List (ValueSort Unit)} {preL preR headL headR : List (List (Ty Unit))}
    (g : Native left carried preL headL out) (h : Native right carried preR headR out)
    (input₁ : Inputs model left) (input₂ : Inputs model right)
    (same : ∀ old, g.step model input₁ old = h.step model input₂ old) (budget : Nat) (old : Inputs model carried) :
    g.evalFrom model input₁ budget old = h.evalFrom model input₂ budget old := by
  induction budget generalizing old with
  | zero => simp only [Loop.Graph.evalFrom, same]
  | succ _ ih =>
    simp only [Loop.Graph.evalFrom, same]
    split
    · rfl
    · exact ih _

theorem optimize_eval (accepted : optimize? loop = some result) (input : Inputs model inputs) (budget : Nat) :
    result.graph.evalBackedges model budget input = loop.evalBackedges model budget input := by
  obtain ⟨built, edited, _, stepped, restored⟩ := optimize_witness accepted
  let prepared := preparedInput loop input
  have unchangedEntry := restore_entry restored
  have initial : result.graph.initial model input = loop.initial model input := by
    simp only [Loop.Graph.initial, Loop.Graph.latch, unchangedEntry.1, unchangedEntry.2.1]
    rfl
  have preparedInit : (prepare loop).initial model prepared = loop.initial model input := prepare_initial input
  have optimizedInit := Pass.step_initial built.view stepped model prepared
  have fromRestored := evalFrom_eq result.graph edited.graph input prepared (restore_step restored input)
    budget (loop.initial model input)
  have fromPrepared := evalFrom_eq (prepare loop) loop prepared input (prepare_step input)
    budget (loop.initial model input)
  calc
    result.graph.evalBackedges model budget input = edited.graph.evalBackedges model budget prepared := by
      simpa only [Loop.Graph.evalBackedges, initial, optimizedInit, preparedInit] using fromRestored
    _ = (prepare loop).evalBackedges model budget prepared := Pass.step_evalBackedges built.view stepped model prepared budget
    _ = loop.evalBackedges model budget input := by
      simpa only [Loop.Graph.evalBackedges, preparedInit] using fromPrepared

theorem normalized_phi_occurrences (built : Built (prepare loop)) (i j : Vertex (prepare loop))
    (entry₁ : Port (carried ++ inputs) (GVN.Cyclic.Builder.sorts (prepare loop) i))
    (entry₂ : Port (carried ++ inputs) (GVN.Cyclic.Builder.sorts (prepare loop) j))
    (back₁ : Source (carried ++ inputs) (GVN.Cyclic.Builder.sorts (prepare loop)) (GVN.Cyclic.Builder.sorts (prepare loop) i))
    (back₂ : Source (carried ++ inputs) (GVN.Cyclic.Builder.sorts (prepare loop)) (GVN.Cyclic.Builder.sorts (prepare loop) j))
    (shape₁ : built.graph.node i = .phi entry₁ back₁) (shape₂ : built.graph.node j = .phi entry₂ back₂)
    (same : FixedPoint.normalize built.graph i = FixedPoint.normalize built.graph j) :
    entry₁.index = entry₂.index ∧ back₁.address.relabel (FixedPoint.normalize built.graph) =
      back₂.address.relabel (FixedPoint.normalize built.graph) := by
  have occurrences := ((FixedPoint.normalize_stable built.graph).1 i j same).2
  simp only [Graph.operandClasses, shape₁, shape₂, Node.addresses, List.map_cons,
    List.map_nil, Address.relabel, List.cons.injEq, Address.argument.injEq] at occurrences
  exact ⟨occurrences.1.2, occurrences.2.1⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
