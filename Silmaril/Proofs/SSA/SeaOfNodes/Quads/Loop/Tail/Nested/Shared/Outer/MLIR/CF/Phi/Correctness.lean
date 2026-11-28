module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Proofs

open SeaOfNodes.Diamond (ValueSort Dataflow)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp opcode)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth lowerCode)
open Silmaril.MLIR.Arith (Atom Width Env Var word)
open Silmaril.MLIR.CF (Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Diamond.MLIR.CF (Label Widths siteFrame)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable {Γ Δ : List Width}

private theorem eval_terminal {Term : List Width → Type} {A : Type}
    (code : Silmaril.MLIR.Pure.Code TargetOp Term Γ) (env : Env Γ) (finish : ∀ {γ}, Term γ → Env γ → A) :
    code.eval evalOp finish env = finish (terminal code).2 (terminalEnv code env) := by
  induction code with
  | terminator => rfl
  | letOp _ _ _ ih => exact ih _

private theorem lowerCode_terminal {args past sigs} {Term : List Width → Type}
    (flow : Dataflow Op args past sigs) (scope : SeaOfNodes.MLIR.Lowering.Scope args past Γ)
    (finish : ∀ {γ}, SeaOfNodes.MLIR.Lowering.Scope args (RVSDG.extend past sigs) γ → Term γ)
    (holds : ∀ {γ}, Term γ → Prop) (ok : ∀ {γ} scope, holds (finish (γ := γ) scope)) :
    holds (terminal (lowerCode opcode flow scope finish)).2 := by
  induction flow generalizing Γ with
  | nil => exact ok scope
  | @cons _ _ _ sort _ _ _ ih => exact ih (scope.pushValue sort) finish ok

private theorem final_jump {site target : Fin size} (path : Chain.Segment src target site)
    (caller : Fin size)
    (direct : path.blocks = [] → (src caller).terminator = .transfer (.jump site)) :
    (src (path.predecessor caller)).terminator = .transfer (.jump target) := by
  induction path generalizing caller with
  | empty => exact direct rfl
  | jump site edge rest ih => exact ih site (fun _ => edge)

private theorem segment_start_mem {site target : Fin size} (path : Chain.Segment src target site)
    (nonempty : path.blocks ≠ []) : site ∈ path.blocks := by
  cases path with
  | empty => exact (nonempty rfl).elim
  | jump => exact List.mem_cons_self

private theorem inner_ne_tail : p.inner ≠ p.stop := by
  have absent := p.distinct
  simp only [List.append_assoc, List.cons_append, List.nil_append] at absent
  have notIn := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp absent).2).2).1
  intro same
  apply notIn
  rw [same]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_left _ (segment_start_mem p.outerSuffix p.outerNonempty)))))

private theorem incoming_jump (taken : Bool) (slot : (p.outerEdgeOccurrence taken).2 = 0)
    (edge : (src (p.outerEdgeOccurrence taken).1).terminator = .transfer (.jump p.stop)) :
    (incoming p taken).isSome = true := by
  unfold incoming predecessor lower Diamond.MLIR.CF.lowerSource
  rw [slot]
  simp only [Diamond.MLIR.CF.lowerBlock, Diamond.MLIR.CF.lowerBlockWith]
  apply lowerCode_terminal _ _ _ (fun t => (atSlot p.stop 0 t).isSome = true)
  intro _ scope
  rw [edge]
  simp [Diamond.MLIR.CF.lowerTerminatorWith, Diamond.MLIR.CF.lowerDestinationWith,
    Diamond.MLIR.CF.fullJump, atSlot, atTarget]

private theorem empty_segment {site target : Fin size} (path : Chain.Segment src target site)
    (caller : Fin size) (empty : path.blocks = []) :
    site = target ∧ path.predecessor caller = caller := by
  cases path with
  | empty => exact ⟨rfl, rfl⟩
  | jump => cases empty

private theorem incoming_false : (incoming p false).isSome = true := by
  by_cases empty : p.outerFalse.blocks = []
  · obtain ⟨target, pred⟩ := empty_segment p.outerFalse p.header empty
    have edge : (src (p.outerFalse.predecessor p.header)).terminator =
        .branch p.outerTest (.jump p.inner) (.jump p.stop) := by
      rw [pred, p.outerEdge, target]
    unfold incoming predecessor lower Diamond.MLIR.CF.lowerSource
    simp only [Program.outerEdgeOccurrence, empty, List.isEmpty_nil]
    simp only [Diamond.MLIR.CF.lowerBlock, Diamond.MLIR.CF.lowerBlockWith]
    apply lowerCode_terminal _ _ _ (fun t => (atSlot p.stop 1 t).isSome = true)
    intro _ scope
    rw [edge]
    simp [Diamond.MLIR.CF.lowerTerminatorWith, Diamond.MLIR.CF.lowerDestinationWith,
      Diamond.MLIR.CF.fullJump, atSlot, atTarget, inner_ne_tail p]
  · have slot : (p.outerEdgeOccurrence false).2 = 0 := by
      simp [Program.outerEdgeOccurrence, List.isEmpty_iff, empty]
    exact incoming_jump p false slot (final_jump p.outerFalse p.header (fun h => (empty h).elim))

theorem rows_exist : ∃ rows, readRows p = some rows := by
  have yes := incoming_jump p true rfl (final_jump p.suffix p.inner (fun empty => (p.nonempty empty).elim))
  refine ⟨_, Option.eq_some_of_isSome ?_⟩
  rw [readRows, dite_eq_left ⟨yes, incoming_false p⟩]
  rfl

private theorem edge_reads {target : Fin size} (edge : Edge (Label regs out size) Γ)
    (args : Operands Γ (Widths regs)) (env : Env Γ) (bank : Env (Widths regs))
    (row : atTarget target edge = some args) (observed : edge.eval env = ⟨.site target, bank⟩) :
    args.eval env = bank := by
  rcases edge with ⟨label, values⟩
  cases label with
  | exit => cases row
  | site id =>
    simp only [atTarget] at row
    split at row
    · rename_i same
      subst id
      cases Option.some.inj row
      cases observed
      rfl
    · cases row

private def siteId : {types : List Width} → Label regs out size types → Option (Fin size)
  | _, .site id => some id
  | _, .exit => none

private theorem edge_cannot_target {target : Fin size} (edge : Edge (Label regs out size) Γ)
    (env : Env Γ) (bank : Env (Widths regs))
    (absent : (atTarget target edge).isNone = true) (observed : edge.eval env = ⟨.site target, bank⟩) : False := by
  have same := congrArg (fun f : Frame (Label regs out size) => siteId f.label) observed
  rcases edge with ⟨label, values⟩
  cases label with
  | exit => cases same
  | site id =>
    change some id = some target at same
    cases Option.some.inj same
    simp [atTarget] at absent

private theorem slot_reads {target : Fin size} {slot : Fin 2}
    (term : Silmaril.MLIR.CF.Terminator (Label regs out size) Δ Γ) (args : Operands Γ (Widths regs))
    (env : Env Γ) (bank : Env (Widths regs)) (row : atSlot target slot term = some args)
    (observed : term.eval env = .inl ⟨.site target, bank⟩) : args.eval env = bank := by
  cases term with
  | ret => cases row
  | br edge =>
    by_cases zero : slot = 0
    · exact edge_reads edge args env bank (by simpa [atSlot, zero] using row) (Sum.inl.inj observed)
    · simp [atSlot, zero] at row
  | condBr test yes no =>
    by_cases zero : slot = 0
    · simp only [atSlot, ite_eq_left zero] at row
      split at row
      · rename_i absent
        by_cases guard : (env.get test).getLsbD 0 = true
        · simp only [Silmaril.MLIR.CF.Terminator.eval, ite_eq_left guard] at observed
          exact edge_reads yes args env bank row (Sum.inl.inj observed)
        · simp only [Silmaril.MLIR.CF.Terminator.eval, ite_eq_right guard] at observed
          exact (edge_cannot_target no env bank absent (Sum.inl.inj observed)).elim
      · cases row
    · simp only [atSlot, ite_eq_right zero] at row
      split at row
      · rename_i absent
        by_cases guard : (env.get test).getLsbD 0 = true
        · simp only [Silmaril.MLIR.CF.Terminator.eval, ite_eq_left guard] at observed
          exact (edge_cannot_target yes env bank absent (Sum.inl.inj observed)).elim
        · simp only [Silmaril.MLIR.CF.Terminator.eval, ite_eq_right guard] at observed
          exact edge_reads no args env bank row (Sum.inl.inj observed)
      · cases row

theorem selected_bank (rows : Rows p) (input old : Bank (regs := regs) model) :
    rows.selectedBank input old = encodeValues (p.outerBank model old (p.toControl.selected model old)) := by
  have observed := CF.outer_arrival p input old
  rw [outerArrival, eval_terminal] at observed
  exact slot_reads _ _ _ _ (rows.checked (arrivalSide (p := p) old)) observed

private theorem look_up {w : Width} (v : Var Γ w) (env : Env Γ)
    (tail : Silmaril.Isotope.LambdaSSA.Semantics.Env Atom) :
    (env.toLambdaSSA tail) v.index = word (env.get v) := by
  induction v with
  | here => cases env; rfl
  | there v ih => cases env; exact ih _

private theorem arguments_read (args : Operands Γ Δ) (env : Env Γ) :
    PhiView.readArguments (arguments args) env.toLambdaSSA = pack (args.eval env) := by
  induction args with
  | nil => rfl
  | cons v rest ih =>
    change Silmaril.Isotope.Value.pair ((env.toLambdaSSA) v.index)
      (PhiView.readArguments (arguments rest) env.toLambdaSSA) =
      .pair (word (env.get v)) (pack (rest.eval env))
    rw [look_up v env, ih]

theorem latch_eq (rows : Rows p) (input old : Bank (regs := regs) model) :
    rows.latch input old = pack (rows.selectedBank input old) :=
  arguments_read _ _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Proofs
