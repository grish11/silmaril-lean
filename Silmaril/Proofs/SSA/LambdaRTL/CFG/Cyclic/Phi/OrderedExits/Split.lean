module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block br)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA (edgeReads)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe v w
variable {V W K J : Type w} {F : Type v} [DecidableEq K] [DecidableEq J]

omit [DecidableEq J] in
theorem header_not_exit (graph : Graph V K F) (exits : List (Option K))
    (partition : checkExits graph exits = true) {key : K}
    (present : (graph.blocks.lookup key).isSome = true) : some key ∉ exits := by
  simp only [checkExits, Bool.and_eq_true, List.all_eq_true] at partition
  intro mem
  have absent := partition.1.2 (some key) mem
  change (graph.blocks.lookup key).isNone = true at absent
  cases found : graph.blocks.lookup key <;> simp [found] at present absent

private def scopeBlock (exits : List (Option K)) (b : Block V K F) : Block V K F :=
  ⟨b.rows, b.body.relabel (scopeLabel exits)⟩

omit [DecidableEq J] in
private theorem lookup_scopeBlock (graph : Graph V K F) (exits : List (Option K)) (key : K) :
    (forScope graph exits).blocks.lookup key = (graph.blocks.lookup key).map (scopeBlock exits) := by
  change (graph.blocks.map fun item => (item.1, scopeBlock exits item.2)).lookup key = _
  induction graph.blocks with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨k, b⟩ := item
    by_cases hit : key == k <;> simp [List.lookup_cons, hit, ih]

omit [DecidableEq J] in
theorem edgeReads_forScope (graph : Graph V K F) (exits : List (Option K)) (pred : Option K) (key : K) :
    edgeReads (forScope graph exits) pred key = edgeReads graph pred key := by
  unfold edgeReads
  rw [lookup_scopeBlock]
  cases graph.blocks.lookup key <;> rfl

omit [DecidableEq J] in
private theorem has_target (exits : List (Option K)) (header : K) (internal : some header ∉ exits)
    (body : CFG.Body V (Option K) F) :
    ((body.relabel (scopeLabel exits)).targets.contains (some header)) =
      body.targets.contains (some header) := by
  have branch (key : Option K) :
      scopeLabel exits key = some header ↔ key = some header := by
    by_cases mem : key ∈ exits
    · have ne (eq : key = some header) : False := internal (eq ▸ mem)
      simpa [scopeLabel, mem] using ne
    · simp [scopeLabel, mem]
  have term (tail : CFG.Term V (Option K) F) :
      some header ∈ (tail.relabel (scopeLabel exits)).targets ↔ some header ∈ tail.targets := by
    induction tail with
    | br key value =>
      simp only [CFG.Term.relabel, CFG.Term.targets, List.mem_singleton]
      exact eq_comm.trans ((branch key).trans eq_comm)
    | case op x l y r ihL ihR => simp [CFG.Term.relabel, CFG.Term.targets, ihL, ihR]
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem]
  induction body with
  | term tail => exact term tail
  | let1 x op rest ih => exact ih
  | let2 x y op rest ih => exact ih

omit [DecidableEq J] in
theorem hasEdge_forScope (plan : Plan V W K J) (graph : Graph V K F) (exits : List (Option K))
    (internal : some plan.header ∉ exits) :
    plan.hasEdge (forScope graph exits) = plan.hasEdge graph := by
  unfold Plan.hasEdge
  cases eq : plan.predecessor with
  | none => exact has_target exits plan.header internal graph.entry
  | some key =>
    rw [Option.elim_some, Option.elim_some, lookup_scopeBlock]
    cases graph.blocks.lookup key with
    | none => rfl
    | some b => exact has_target exits plan.header internal b.body

omit [DecidableEq K] [DecidableEq J] in
private theorem forward_not_exit (plan : Plan V W K J) (exits : List (Option K)) :
    some plan.forward ∉ exits.map (Option.map plan.label) := by
  intro mem
  obtain ⟨key, _, eq⟩ := List.mem_map.mp mem
  cases key with
  | none => cases eq
  | some k => exact plan.fresh k (Option.some.inj eq)

private theorem scope_route (plan : Plan V W K J) (exits : List (Option K))
    (internal : some plan.header ∉ exits) (pred key : Option K) :
    scopeLabel (exits.map (Option.map plan.label)) (plan.route pred key) =
      plan.route pred (scopeLabel exits key) := by
  have mapped (key : Option K) : key.map plan.label ∈ exits.map (Option.map plan.label) ↔ key ∈ exits := by
    simp [List.mem_map, (Option.map_injective plan.label.injective).eq_iff]
  cases key with
  | none => simp [Plan.route, scopeLabel]
  | some k =>
    by_cases selected : plan.selected pred k
    · have same := selected.2
      subst k
      simp [Plan.route, scopeLabel, internal, selected, forward_not_exit]
    · by_cases mem : some k ∈ exits
      · have im : some (plan.label k) ∈ exits.map (Option.map plan.label) := (mapped (some k)).2 mem
        simp [Plan.route, scopeLabel, mem, im, selected]
      · have im : some (plan.label k) ∉ exits.map (Option.map plan.label) :=
          fun hit => mem ((mapped (some k)).1 hit)
        simp [Plan.route, scopeLabel, mem, im, selected]

omit [DecidableEq K] [DecidableEq J] in
private theorem rename_relabel (plan : Plan V W K J) (route : Option K → Option J)
    (src : Option K → Option K) (dst : Option J → Option J)
    (comm : ∀ key, dst (route key) = route (src key)) (body : CFG.Body V (Option K) F) :
    (plan.renameBody route body).relabel dst = plan.renameBody route (body.relabel src) := by
  have term (tail : CFG.Term V (Option K) F) :
      (plan.renameTerm route tail).relabel dst = plan.renameTerm route (tail.relabel src) := by
    induction tail <;> simp [Plan.renameTerm, CFG.Term.relabel, *]
  induction body <;> simp [Plan.renameBody, CFG.Body.relabel, *]

theorem forScope_rewrite (plan : Plan V W K J) (graph : Graph V K F) (exits : List (Option K))
    (internal : some plan.header ∉ exits) :
    forScope (plan.rewrite graph) (exits.map (Option.map plan.label)) =
      plan.rewrite (forScope graph exits) := by
  let mapped := exits.map (Option.map plan.label)
  have body (pred : Option K) (b : CFG.Body V (Option K) F) :
      (plan.renameBody (plan.route pred) b).relabel (scopeLabel mapped) =
      plan.renameBody (plan.route pred) (b.relabel (scopeLabel exits)) :=
    rename_relabel plan _ _ _ (scope_route plan exits internal pred) b
  have forward (pred : Option K) :
      (plan.forwardAt (F := F) pred).map (fun (item : J × Block W J F) => (item.1, scopeBlock mapped item.2)) = plan.forwardAt pred := by
    have header : some (plan.label plan.header) ∉ mapped := by
      intro mem
      obtain ⟨key, belongs, eq⟩ := List.mem_map.mp mem
      have same : key = some plan.header := Option.map_injective plan.label.injective eq
      exact internal (same ▸ belongs)
    by_cases selected : pred = plan.predecessor
    · simp [Plan.forwardAt, selected, Plan.forwardBlock, br, scopeBlock, CFG.Body.relabel, CFG.Term.relabel,
        scopeLabel, header]
    · simp [Plan.forwardAt, selected]
  unfold forScope Plan.rewrite
  change Graph.mk _ ((plan.forwardAt none ++ graph.blocks.flatMap _).map
      (fun (item : J × Block W J F) => (item.1, scopeBlock mapped item.2))) =
    Graph.mk _ (plan.forwardAt none ++ (graph.blocks.map (fun item => (item.1, scopeBlock exits item.2))).flatMap _)
  rw [body none, List.map_append, forward none]
  congr 2
  induction graph.blocks with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨k, b⟩ := item
    simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.map_append, forward, ih]
    simp only [Plan.renameBlock, scopeBlock, body (some k)]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.Split
