module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.InstructionMap.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.InstructionMap.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body Term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA

universe v w
variable {V K : Type w} {F G : Type v} (f : F → G)

private theorem term_targets (term : Term V (Option K) F) :
    (term.mapOp f).targets = term.targets := by
  induction term with
  | br => rfl
  | case op x lhs y rhs hl hr => simp [Term.mapOp, Term.targets, hl, hr]

private theorem body_targets (body : Body V (Option K) F) :
    (body.mapOp f).targets = body.targets := by
  induction body with
  | term term => exact term_targets f term
  | let1 x op b ih => exact ih
  | let2 x y op b ih => exact ih

private theorem lookup_map (table : List (K × Block V K F)) [DecidableEq K] (key : K) :
    (table.map fun (label, block) => (label, block.mapOp f)).lookup key =
      (table.lookup key).map (Block.mapOp f) := by
  induction table with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨label, block⟩
    cases eq : (key == label) <;> simp [List.lookup, eq, ih]

private theorem map_entry (graph : Graph V K F) :
    (graph.mapOp f).entry = graph.entry.mapOp f := rfl

private theorem map_blocks (graph : Graph V K F) :
    (graph.mapOp f).blocks = graph.blocks.map (fun (key, block) => (key, block.mapOp f)) := rfl

variable [DecidableEq K]

private theorem predecessors_map (graph : Graph V K F) (key : K) :
    (graph.mapOp f).predecessors key = graph.predecessors key := by
  simp [Graph.predecessors, map_entry, map_blocks, List.filterMap_map, Block.mapOp, body_targets]

theorem check_map (graph : Graph V K F) [DecidableEq V] :
    (graph.mapOp f).check = graph.check := by
  simp only [Graph.check]
  simp [map_entry, map_blocks, Block.mapOp, List.map_map, List.all_map, Function.comp_def, body_targets,
    predecessors_map]

private theorem edgePacket_map (graph : Graph V K F) (src : Option K) (key : K) :
    edgePacket (graph.mapOp f) src key = edgePacket graph src key := by
  simp only [edgePacket, map_blocks, lookup_map]
  cases graph.blocks.lookup key <;> rfl

private theorem liftOp_map (o : Op V F) : liftOp (o.mapOp f) = (liftOp o).mapOp f := by
  cases o <;> rfl

private theorem lowerTerm_map (graph : Graph V K F) (src : Option K) (term : Term V (Option K) F) :
    lowerTerm (graph.mapOp f) src (term.mapOp f) = (lowerTerm graph src term).mapOp f := by
  unfold lowerTerm
  induction term with
  | br key value => cases key <;> simp [Term.mapOp, liftTerm, edgePacket_map]
  | case o x lhs y rhs hl hr => simp [Term.mapOp, liftTerm, liftOp_map, hl, hr]

private theorem lowerBody_map (graph : Graph V K F) (src : Option K) (body : Body V (Option K) F) :
    lowerBody (graph.mapOp f) src (body.mapOp f) = (lowerBody graph src body).mapOp f := by
  unfold lowerBody
  induction body with
  | term term => exact congrArg Body.term (lowerTerm_map f graph src term)
  | let1 x op b ih => simp [Body.mapOp, liftBody, liftOp_map, ih]
  | let2 x y op b ih => simp [Body.mapOp, liftBody, liftOp_map, ih]

omit [DecidableEq K] in
private theorem decode_map (rows : List (Row V K)) (body : Body (Option V) (Option K) F) :
    decode rows (body.mapOp f) = (decode rows body).mapOp f := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [decode, Body.mapOp, Op.mapOp, ih]

theorem lower_map (graph : Graph V K F) :
    lower (graph.mapOp f) = (lower graph).mapOp f := by
  simp [lower, lowerBlock, map_entry, map_blocks, Block.mapOp, CFG.mapOp, CFG.Block.mapOp,
    List.map_map, lowerBody_map, decode_map]

private theorem op_reads (op : Op V F) : (op.mapOp f).fvList = op.fvList := by
  cases op <;> rfl

omit [DecidableEq K] in
private theorem term_definitions (term : Term V (Option K) F) :
    termDefinitions (term.mapOp f) = termDefinitions term := by
  induction term with
  | br => rfl
  | case op x lhs y rhs hl hr => simp [termDefinitions, Term.mapOp, hl, hr]

omit [DecidableEq K] in
private theorem body_definitions (body : Body V (Option K) F) :
    bodyDefinitions (body.mapOp f) = bodyDefinitions body := by
  induction body with
  | term term => exact term_definitions f term
  | let1 x op b ih => simp [bodyDefinitions, Body.mapOp, ih]
  | let2 x y op b ih => simp [bodyDefinitions, Body.mapOp, ih]

omit [DecidableEq K] in
private theorem definitions_map (graph : Graph V K F) (inputs : List V) :
    definitions (graph.mapOp f) inputs = definitions graph inputs := by
  simp [definitions, map_entry, map_blocks, List.flatMap_map, Block.mapOp, body_definitions]

omit [DecidableEq K] in
private theorem term_routes (reads : K → List V) (term : Term V (Option K) F) :
    termRoutes reads (term.mapOp f) = termRoutes reads term := by
  induction term with
  | br key val => cases key <;> rfl
  | case op x lhs y rhs hl hr => simp [termRoutes, Term.mapOp, op_reads, hl, hr]

omit [DecidableEq K] in
private theorem body_routes (reads : K → List V) (body : Body V (Option K) F) :
    bodyRoutes reads (body.mapOp f) = bodyRoutes reads body := by
  induction body with
  | term term => exact term_routes f reads term
  | let1 x op b ih => simp [bodyRoutes, Body.mapOp, op_reads, ih]
  | let2 x y op b ih => simp [bodyRoutes, Body.mapOp, op_reads, ih]

private theorem edgeReads_map (graph : Graph V K F) (src : Option K) (key : K) :
    edgeReads (graph.mapOp f) src key = edgeReads graph src key := by
  simp only [edgeReads, map_blocks, lookup_map]
  cases graph.blocks.lookup key <;> rfl

private theorem routes_map (graph : Graph V K F) (src : Option K) :
    routes (graph.mapOp f) src = routes graph src := by
  have reads : edgeReads (graph.mapOp f) src = edgeReads graph src := funext (edgeReads_map f graph src)
  cases src with
  | none => simp [routes, reads, map_entry, body_routes]
  | some key =>
    simp only [routes, reads, map_blocks, lookup_map]
    cases graph.blocks.lookup key <;> simp [Block.mapOp, body_routes]

private theorem path_unmap {graph : Graph V K F} {src : Option K} {accesses : List (Access V)}
    (path : EntryPath (graph.mapOp f) src accesses) : EntryPath graph src accesses := by
  induction path with
  | entry => exact .entry
  | follow path chosen edge ih => exact .follow ih (by simpa only [routes_map] using chosen) edge

theorem wellFormed_map (graph : Graph V K F) [DecidableEq V] (inputs : List V)
    (wf : WellFormed graph inputs) : WellFormed (graph.mapOp f) inputs :=
  ⟨(check_map f graph).trans wf.normalized, by simpa only [definitions_map] using wf.unique,
    fun path chosen => wf.available (path_unmap f path) (by simpa only [routes_map] using chosen)⟩

theorem checkArrivals_map (graph : Graph V K F) [DecidableEq V] (inputs : List V)
    (certificate : Certificate V K) :
    GlobalSSA.check (graph.mapOp f) inputs certificate = GlobalSSA.check graph inputs certificate := by
  simp [GlobalSSA.check, check_map, definitions_map, routes_map, map_blocks, lookup_map]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi
