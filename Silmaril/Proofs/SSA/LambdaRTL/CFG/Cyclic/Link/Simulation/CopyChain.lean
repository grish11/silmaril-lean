module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.PacketCopy
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Soundness
import Mathlib.Data.Fintype.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison

variable {V F α : Type} [DecidableEq V] {a b : Nat}
variable {graph : Graph V F a b}

theorem next_iff {index : Fin graph.locals} {target : Label graph.locals b} :
    next? graph index = some target ↔
      PacketCopy.Forwards {(graph.block index).param} (graph.block index).body target :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.target_iff

private theorem path_trace_unique {start : Label graph.locals b}
    {first second : List (Fin graph.locals)} {port port' : Fin b}
    (path : Path graph start first port) (other : Path graph start second port') :
    first = second := by
  induction path generalizing second port' with
  | exit port => cases other; rfl
  | step edge tail ih =>
    cases other with
    | step edge' tail' =>
      cases Option.some.inj (next_iff.mpr edge |>.symm.trans (next_iff.mpr edge'))
      rw [ih tail']

private theorem path_suffix {start : Label graph.locals b} {trace : List (Fin graph.locals)}
    {port : Fin b} (path : Path graph start trace port) {index : Fin graph.locals}
    (visited : index ∈ trace) :
    ∃ suffix, suffix.length ≤ trace.length ∧ Path graph (.inl index) suffix port := by
  induction path with
  | exit port => simp at visited
  | @step head next rest port edge tail ih =>
    rcases List.mem_cons.mp visited with rfl | later
    · exact ⟨index :: rest, le_rfl, .step edge tail⟩
    · obtain ⟨suffix, shorter, fromIndex⟩ := ih later
      exact ⟨suffix, shorter.trans (Nat.le_succ _), fromIndex⟩

private theorem path_nodup {start : Label graph.locals b} {trace : List (Fin graph.locals)}
    {port : Fin b} (path : Path graph start trace port) : trace.Nodup := by
  induction path with
  | exit port => simp
  | @step index next rest port edge tail ih =>
    refine List.nodup_cons.mpr ⟨fun visited => ?_, ih⟩
    obtain ⟨suffix, shorter, fromIndex⟩ := path_suffix tail visited
    have same := path_trace_unique (Path.step edge tail) fromIndex
    rw [← same] at shorter
    exact Nat.not_succ_le_self _ shorter

private theorem bounded_of_path {start : Label graph.locals b} {trace : List (Fin graph.locals)}
    {port : Fin b} (path : Path graph start trace port) {fuel : Nat} (enough : trace.length ≤ fuel) :
    terminalWithin? graph fuel start = some port := by
  induction path generalizing fuel with
  | exit port => cases fuel <;> rfl
  | step edge tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => simp [terminalWithin?, next_iff.mpr edge, ih (Nat.le_of_succ_le_succ enough)]

private theorem path_of_bounded {fuel : Nat} {start : Label graph.locals b} {port : Fin b}
    (found : terminalWithin? graph fuel start = some port) :
    ∃ trace, Path graph start trace port := by
  induction fuel generalizing start with
  | zero =>
    cases start with
    | inl index => simp [terminalWithin?] at found
    | inr exit =>
      have same : exit = port := Option.some.inj found
      exact ⟨[], same ▸ Path.exit exit⟩
  | succ fuel ih =>
    cases start with
    | inr exit =>
      have same : exit = port := Option.some.inj found
      exact ⟨[], same ▸ Path.exit exit⟩
    | inl index =>
      cases edge : next? graph index with
      | none => simp [terminalWithin?, edge] at found
      | some next =>
        obtain ⟨trace, tail⟩ := ih (by simpa [terminalWithin?, edge] using found)
        exact ⟨index :: trace, .step (next_iff.mp edge) tail⟩

theorem terminal_iff {start : Label graph.locals b} {port : Fin b} :
    terminal? graph start = some port ↔ ∃ trace, Path graph start trace port := by
  refine ⟨path_of_bounded, ?_⟩
  rintro ⟨trace, path⟩
  exact bounded_of_path path (by simpa using (path_nodup path).length_le_card)

private theorem terminal_public (graph : Graph V F a b) (port : Fin b) :
    terminal? graph (.inr port) = some port :=
  terminal_iff.mpr ⟨[], .exit port⟩

private theorem path_run (model : Model F Part α) (packet : α)
    {start : Label graph.locals b} {trace : List (Fin graph.locals)} {port : Fin b}
    (path : Path graph start trace port) :
    iter (graph.step model) (start, packet) = pure (port, packet) := by
  induction path with
  | exit port =>
    rw [congrFun (LawfulElgotMonad.fixpoint _) _]
    simp [Graph.step]
  | @step index next rest port typed tail ih =>
    rw [congrFun (LawfulElgotMonad.fixpoint _) _, Simulation.forwardingStep model index next packet typed]
    rw [← Part.pure_eq_some, pure_bind]
    exact ih

theorem denote_of_terminal (model : Model F Part α) (input : Fin a × α) (port : Fin b)
    (found : terminal? graph (graph.entry input.1) = some port) :
    graph.denote model input = pure (port, input.2) := by
  obtain ⟨trace, path⟩ := terminal_iff.mp found
  exact path_run model input.2 path

private theorem path_of_run (model : Model F Part α)
    (typed : ∀ i, (next? graph i).isSome) {start : Label graph.locals b × α} {result : Fin b × α}
    (run : Silmaril.Elgot.Part.Runs (graph.step model) start result) :
    ∃ trace, Path graph start.1 trace result.1 := by
  induction run with
  | @done start result returned =>
    rcases start with ⟨index | port, packet⟩
    · simp [Graph.step, Part.mem_map_iff] at returned
    · have same : result = (port, packet) := by simpa [Graph.step] using returned
      subst result
      exact ⟨[], .exit port⟩
  | @more start next result advanced _ ih =>
    rcases start with ⟨index | port, packet⟩
    · obtain ⟨target, edge⟩ := Option.isSome_iff_exists.mp (typed index)
      have forwards := next_iff.mp edge
      rw [Simulation.forwardingStep model index target packet forwards] at advanced
      have same : next = (target, packet) := by simpa using advanced
      subst next
      obtain ⟨trace, tail⟩ := ih
      exact ⟨index :: trace, .step forwards tail⟩
    · simp [Graph.step] at advanced

theorem denote_none (model : Model F Part α) (input : Fin a × α)
    (typed : ∀ i, (next? graph i).isSome) (missing : terminal? graph (graph.entry input.1) = none) :
    graph.denote model input = Part.none := by
  apply Part.eq_none_iff.mpr
  intro result member
  have run := (Silmaril.Elgot.Part.mem_iter_iff (graph.step model) _ result).mp member
  have found := terminal_iff.mpr (path_of_run model typed run)
  rw [missing] at found
  contradiction

theorem check_iff (graph : Graph V F a b) (wire : Fin a → Fin b) :
    check graph wire = true ↔ Total graph ∧
      ∀ input, terminal? graph (graph.entry input) = some (wire input) := by
  simp [check, Total, Bool.and_eq_true, List.all_eq_true]

private theorem route_terminal (total : Total graph) (label : Label graph.locals b) :
    terminal? graph label = some (Sum.elim (terminalPort graph total) id label) := by
  cases label with
  | inl index => exact (Option.some_get (total index)).symm
  | inr port => exact terminal_public graph port

theorem certificate_entry {wire : Fin a → Fin b} (passed : check graph wire = true) (total : Total graph)
    (input : Fin a) :
    Sum.elim (fun index => .inr (terminalPort graph total index)) Sum.inr (graph.entry input) =
      (Graph.wiring (V := V) (F := F) wire).entry input := by
  have found := route_terminal total (graph.entry input)
  rw [(check_iff graph wire).mp passed |>.2 input] at found
  have same := Option.some.inj found
  have route (label : Label graph.locals b) :
      Sum.elim (fun index => Sum.inr (terminalPort graph total index)) Sum.inr label =
        (Sum.inr (Sum.elim (terminalPort graph total) id label) : Label 0 b) := by
    cases label <;> rfl
  exact (route (graph.entry input)).trans (congrArg Sum.inr same.symm)

theorem certificate_block (wire : Fin a → Fin b) (total : Total graph) (index : Fin graph.locals) :
    BlockMatch (Graph.wiring (V := V) (F := F) wire)
      (Sum.elim (fun i => .inr (terminalPort graph total i)) Sum.inr)
      (graph.block index) (.inr (terminalPort graph total index)) := by
  obtain ⟨trace, path⟩ := terminal_iff.mp (route_terminal total (.inl index))
  cases path with
  | @step _ next rest _ typed tail =>
    have same := Option.some.inj ((terminal_iff.mpr ⟨rest, tail⟩).symm.trans (route_terminal total next))
    apply BlockMatch.forwardCopies next typed
    cases next <;> exact congrArg Sum.inr same

theorem check_complete (model : PairModel F Part α) (graph : Graph V F a b)
    (wire : Fin a → Fin b) (total : Total graph)
    (included : Refines (Quotient.mk _ graph : Arrow V F α a b)
      (Quotient.mk _ (Graph.wiring wire))) :
    check graph wire = true := by
  refine (check_iff graph wire).mpr ⟨total, fun input => ?_⟩
  have found := route_terminal total (graph.entry input)
  have atInput := included model (input, model.val.unit)
  change graph.denote model.val (input, model.val.unit) ≤
    (Graph.wiring (V := V) (F := F) wire).denote model.val (input, model.val.unit) at atInput
  rw [denote_of_terminal model.val (input, model.val.unit) _ found,
    Simulation.denote_wiring] at atInput
  have same := Part.mem_some_iff.mp (atInput _ (Part.mem_some _))
  exact found.trans (congrArg (fun output : Fin b × α => some output.1) same)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain
