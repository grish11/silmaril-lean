module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.Arrival

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split (splitCertificate)
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe u v
variable {V W K J : Type u} {F : Type v}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
variable (plan : Plan V W K J) (graph : Graph V K F)

private def renameAccess (f : V → W) : Access V → Access W
  | .read names => .read (names.map f)
  | .define names => .define (names.map f)

omit [DecidableEq K] [DecidableEq J] in
private theorem renamed_reads (names available : List V) :
    (names.map plan.register).all (fun name => (available.map plan.register).contains name) =
      names.all (fun name => available.contains name) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.all_eq_true]

omit [DecidableEq K] [DecidableEq J] in
private theorem rename_scan (events : List (Access V)) (available : List V) :
    Access.scan (available.map plan.register) (events.map (renameAccess plan.register)) =
      (Access.scan available events).map (List.map plan.register) := by
  induction events generalizing available with
  | nil => rfl
  | cons event events ih =>
    cases event with
    | read names =>
      simp only [List.map_cons, renameAccess, Access.scan, renamed_reads, ih]
      split <;> rfl
    | define names =>
      simpa only [List.map_cons, renameAccess, Access.scan, List.map_append] using ih (available ++ names)

omit [DecidableEq K] [DecidableEq J] [DecidableEq W] in
private theorem scan_append (available : List V) (left right : List (Access V)) :
    Access.scan available (left ++ right) =
      (Access.scan available left).bind (fun seen => Access.scan seen right) := by
  induction left generalizing available with
  | nil => rfl
  | cons front rest ih =>
    cases front with
    | read names =>
      by_cases allowed : names.all (fun n => available.contains n) = true
      · simpa only [List.cons_append, Access.scan, ite_eq_left allowed] using ih available
      · simp only [List.cons_append, Access.scan, ite_eq_right allowed, Option.bind_none]
    | define names => exact ih (available ++ names)

omit [DecidableEq V] [DecidableEq W] in
private theorem lookup_renamed_claim (cert : Certificate V K) (target : K) :
    (splitCertificate plan graph cert).lookup (plan.label target) =
      (cert.lookup target).map (List.map plan.register) := by
  have renamed : (cert.map fun (key, names) => (plan.label key, names.map plan.register)).lookup
      (plan.label target) = (cert.lookup target).map (List.map plan.register) := by
    induction cert with
    | nil => rfl
    | cons claim cert ih =>
      obtain ⟨key, names⟩ := claim
      by_cases h : key = target
      · subst key
        simp
      · have missed := beq_eq_false_iff_ne.mpr (Ne.symm h)
        have renamedMissed := beq_eq_false_iff_ne.mpr (fun eq => (Ne.symm h) (plan.label.injective eq))
        simp only [List.map_cons, List.lookup_cons, missed, renamedMissed, ih]
  unfold splitCertificate
  cases cert.lookup plan.header with
  | none => exact renamed
  | some required =>
    rw [List.lookup_cons, beq_eq_false_iff_ne.mpr (plan.fresh target)]
    exact renamed

omit [DecidableEq V] [DecidableEq W] in
private theorem lookup_forward_claim (cert : Certificate V K) {required : List V}
    (found : cert.lookup plan.header = some required) :
    (splitCertificate plan graph cert).lookup plan.forward =
      some ((required ++ edgeReads graph plan.predecessor plan.header).map plan.register) := by
  simp [splitCertificate, found]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem rename_value_reads (f : V → W) (value : Val V) :
    (value.rename f).fvList = value.fvList.map f := by
  induction value <;> simp [Val.rename, Val.fvList, *]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem rename_op_reads (f : V → W) (op : Op V F) :
    (op.rename f).fvList = op.fvList.map f := by
  cases op <;> simp [Op.rename, Op.fvList, rename_value_reads]

omit [DecidableEq V] [DecidableEq W] in
private theorem renamed_edge_reads (pred : Option K) (target : K) :
    edgeReads (plan.rewrite graph) (plan.rekey target pred) (plan.label target) =
      (edgeReads graph pred target).map plan.register := by
  unfold edgeReads
  rw [plan.lookup_renamed]
  cases graph.blocks.lookup target with
  | none => rfl
  | some block =>
    change (arguments (plan.rekey target pred) (block.rows.map (plan.renameRow target))).flatMap
      Val.fvList = ((arguments pred block.rows).flatMap Val.fvList).map plan.register
    induction block.rows with
    | nil => rfl
    | cons row rows ih =>
      simp only [List.map_cons, arguments, List.flatMap_cons, plan.operand_rename,
        rename_value_reads, List.map_append]
      simp only [arguments] at ih
      rw [ih]

omit [DecidableEq V] [DecidableEq W] in
private theorem forwarded_edge_reads (edge : plan.hasEdge graph = true) (pred : Option J) :
    edgeReads (plan.rewrite graph) pred plan.forward = [] := by
  simp [edgeReads, plan.lookup_forward graph edge, Plan.forwardBlock, arguments]

/-- A related route is either a pure renaming or the selected route with its
last φ read moved to the fresh forwarding block. -/
private inductive RouteMatch (plan : Plan V W K J) (pred : Option K) (moved : List V) :
    Route V K → Route W J → Prop where
  | renamed (key : Option K) (events : List (Access V)) :
      RouteMatch plan pred moved ⟨key, events⟩ ⟨key.map plan.label, events.map (renameAccess plan.register)⟩
  | forwarded (selected : pred = plan.predecessor) (before : List (Access V)) :
      RouteMatch plan pred moved ⟨some plan.header, before ++ [.read moved]⟩
        ⟨some plan.forward, before.map (renameAccess plan.register) ++ [.read []]⟩

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem RouteMatch.prepend {pred : Option K} {moved : List V} {a : Route V K} {b : Route W J}
    (matchRoute : RouteMatch plan pred moved a b) (front : List (Access V)) :
    RouteMatch plan pred moved { a with accesses := front ++ a.accesses }
      { b with accesses := front.map (renameAccess plan.register) ++ b.accesses } := by
  cases matchRoute with
  | renamed key events =>
    simpa only [List.map_append] using
      (RouteMatch.renamed (plan := plan) (pred := pred) (moved := moved) key (front ++ events))
  | forwarded selected before =>
    simpa only [List.map_append, List.append_assoc] using
      (RouteMatch.forwarded (plan := plan) (moved := moved) selected (front ++ before))

omit [DecidableEq V] [DecidableEq W] in
private theorem term_routes (edge : plan.hasEdge graph = true) (pred : Option K)
    (term : CFG.Term V (Option K) F) {out : Route W J}
    (member : out ∈ termRoutes (edgeReads (plan.rewrite graph) (pred.map plan.label))
      (plan.renameTerm (plan.route pred) term)) :
    ∃ old ∈ termRoutes (edgeReads graph pred) term,
      RouteMatch plan pred (edgeReads graph pred plan.header) old out := by
  induction term generalizing out with
  | br key value =>
    cases key with
    | none =>
      simp only [Plan.renameTerm, Plan.route, Option.map_none, termRoutes, List.mem_singleton] at member
      subst out
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simpa only [Option.map_none, List.map_cons, List.map_nil, renameAccess, rename_value_reads] using
        (RouteMatch.renamed (plan := plan) (pred := pred) (moved := edgeReads graph pred plan.header)
          none [.read value.fvList])
    | some target =>
      by_cases chosen : plan.selected pred target
      · obtain ⟨samePred, rfl⟩ := chosen
        have hit : plan.selected pred plan.header := ⟨samePred, rfl⟩
        simp only [Plan.renameTerm, Plan.route, Option.map_some, ite_eq_left hit,
          termRoutes, List.mem_singleton, forwarded_edge_reads plan graph edge] at member
        subst out
        exact ⟨_, List.mem_singleton_self _, RouteMatch.forwarded samePred []⟩
      · have read := renamed_edge_reads plan graph pred target
        rw [plan.rekey_other chosen] at read
        simp only [Plan.renameTerm, Plan.route, Option.map_some, ite_eq_right chosen,
          termRoutes, List.mem_singleton, read] at member
        subst out
        exact ⟨_, List.mem_singleton_self _, RouteMatch.renamed _ _⟩
  | case op x left y right ihL ihR =>
    simp only [Plan.renameTerm, termRoutes, List.mem_append, List.mem_map] at member ⊢
    rcases member with ⟨r, ok, rfl⟩ | ⟨r, ok, rfl⟩
    · obtain ⟨old, mem, related⟩ := ihL ok
      exact ⟨_, Or.inl ⟨old, mem, rfl⟩,
        by simpa only [rename_op_reads, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil, renameAccess] using related.prepend plan [.read op.fvList, .define [x]]⟩
    · obtain ⟨old, mem, related⟩ := ihR ok
      exact ⟨_, Or.inr ⟨old, mem, rfl⟩,
        by simpa only [rename_op_reads, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil, renameAccess] using related.prepend plan [.read op.fvList, .define [y]]⟩

omit [DecidableEq V] [DecidableEq W] in
private theorem body_routes (edge : plan.hasEdge graph = true) (pred : Option K)
    (body : CFG.Body V (Option K) F) {out : Route W J}
    (member : out ∈ bodyRoutes (edgeReads (plan.rewrite graph) (pred.map plan.label))
      (plan.renameBody (plan.route pred) body)) :
    ∃ old ∈ bodyRoutes (edgeReads graph pred) body,
      RouteMatch plan pred (edgeReads graph pred plan.header) old out := by
  induction body generalizing out with
  | term term => exact term_routes plan graph edge pred term member
  | let1 x op rest ih =>
    obtain ⟨r, ok, rfl⟩ := List.mem_map.mp member
    obtain ⟨old, mem, related⟩ := ih ok
    exact ⟨_, List.mem_map.mpr ⟨old, mem, rfl⟩,
      by simpa only [rename_op_reads, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, renameAccess] using related.prepend plan [.read op.fvList, .define [x]]⟩
  | let2 x y op rest ih =>
    obtain ⟨r, ok, rfl⟩ := List.mem_map.mp member
    obtain ⟨old, mem, related⟩ := ih ok
    exact ⟨_, List.mem_map.mpr ⟨old, mem, rfl⟩,
      by simpa only [rename_op_reads, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, renameAccess] using related.prepend plan [.read op.fvList, .define [x, y]]⟩

omit [DecidableEq V] [DecidableEq W] in
private theorem routes_match (edge : plan.hasEdge graph = true) (pred : Option K)
    {out : Route W J} (member : out ∈ routes (plan.rewrite graph) (pred.map plan.label)) :
    ∃ old ∈ routes graph pred, RouteMatch plan pred (edgeReads graph pred plan.header) old out := by
  cases pred with
  | none => exact body_routes plan graph edge none graph.entry member
  | some key =>
    simp only [Option.map_some, routes, plan.lookup_renamed] at member
    cases found : graph.blocks.lookup key with
    | none => simp [found] at member
    | some block =>
      simp only [found, Option.map_some, Option.elim_some, Plan.renameBlock] at member
      obtain ⟨r, mem, rfl⟩ := List.mem_map.mp member
      obtain ⟨old, oldMem, related⟩ := body_routes plan graph edge (some key) block.body mem
      refine ⟨{ old with accesses := .define (block.rows.map Row.dst) :: old.accesses }, ?_, ?_⟩
      · simp only [routes, found, Option.elim_some]
        exact List.mem_map.mpr ⟨old, oldMem, rfl⟩
      · simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          renameAccess, List.map_map, Function.comp_def, Plan.renameRow] using
          related.prepend plan [.define (block.rows.map Row.dst)]

private theorem checks_related (cert : Certificate V K) (available : List V) (pred : Option K)
    {old : Route V K} {out : Route W J}
    (related : RouteMatch plan pred (edgeReads graph pred plan.header) old out)
    (checked : checkRoute cert available old = true) :
    checkRoute (splitCertificate plan graph cert) (available.map plan.register) out = true := by
  cases related with
  | renamed key events =>
    simp only [checkRoute, rename_scan] at ⊢
    cases ran : Access.scan available events with
    | none => simp [checkRoute, ran] at checked
    | some seen =>
      cases key with
      | none => rfl
      | some target =>
        cases found : cert.lookup target with
        | none => simp [checkRoute, ran, found] at checked
        | some required =>
          simpa only [checkRoute, ran, Option.map_some, Option.any_some, Option.elim_some,
            lookup_renamed_claim, found, renamed_reads] using checked
  | forwarded selected before =>
    have checkedPrefix := checked
    simp only [checkRoute, scan_append] at checkedPrefix
    cases ran : Access.scan available before with
    | none => simp [ran] at checkedPrefix
    | some seen =>
      have ran' : Access.scan (available.map plan.register) (before.map (renameAccess plan.register)) =
          some (seen.map plan.register) := by rw [rename_scan, ran]; rfl
      by_cases reads : (edgeReads graph pred plan.header).all (fun n => seen.contains n) = true
      · cases found : cert.lookup plan.header with
        | none =>
          simp only [ran, Option.bind_some, Access.scan, ite_eq_left reads,
            Option.any_some, Option.elim_some, found, Option.any_none, Bool.false_eq_true] at checkedPrefix
        | some required =>
          have req : required.all (fun n => seen.contains n) = true := by
            simpa only [ran, Option.bind_some, Access.scan, ite_eq_left reads, Option.any_some,
              Option.elim_some, found] using checkedPrefix
          rw [selected] at reads
          simp only [checkRoute, scan_append, ran', Option.bind_some, Access.scan, List.all_nil,
            ite_true, Option.any_some, Option.elim_some, lookup_forward_claim plan graph cert found,
            renamed_reads, List.all_append, req, reads, Bool.and_self]
      · simp only [ran, Option.bind_some, Access.scan, ite_eq_right reads,
          Option.any_none, Bool.false_eq_true] at checkedPrefix

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem definitions_term (route : Option K → Option J) (term : CFG.Term V (Option K) F) :
    termDefinitions (plan.renameTerm route term) = (termDefinitions term).map plan.register := by
  induction term <;> simp [Plan.renameTerm, termDefinitions, *]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem definitions_body (route : Option K → Option J) (body : CFG.Body V (Option K) F) :
    bodyDefinitions (plan.renameBody route body) = (bodyDefinitions body).map plan.register := by
  induction body <;> simp [Plan.renameBody, bodyDefinitions, definitions_term, *]

omit [DecidableEq V] [DecidableEq W] [DecidableEq J] in
private theorem definitions_renamed (inputs : List V) :
    definitions (plan.rewrite graph) (inputs.map plan.register) =
      (definitions graph inputs).map plan.register := by
  let blockDefs := fun (item : J × Block W J F) => item.2.rows.map Row.dst ++ bodyDefinitions item.2.body
  have noDefs (pred : Option K) : (plan.forwardAt pred).flatMap blockDefs = [] := by
    by_cases hit : pred = plan.predecessor
    · simp [Plan.forwardAt, hit, Plan.forwardBlock, br, blockDefs, bodyDefinitions, termDefinitions]
    · simp [Plan.forwardAt, hit]
  simp only [definitions, Plan.rewrite, definitions_body, List.map_append, List.flatMap_append]
  change inputs.map plan.register ++ (bodyDefinitions graph.entry).map plan.register ++
      ((plan.forwardAt none).flatMap blockDefs ++ (graph.blocks.flatMap _).flatMap blockDefs) = _
  rw [noDefs, List.nil_append]
  congr 2
  induction graph.blocks with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨key, block⟩ := item
    simp only [List.flatMap_cons, List.flatMap_append, noDefs, List.nil_append, List.map_append]
    rw [ih]
    simp [blockDefs, Plan.renameBlock, Plan.renameRow, definitions_body, Function.comp_def]

omit [DecidableEq V] [DecidableEq W] [DecidableEq J] in
private theorem splitCert_unique (cert : Certificate V K) (unique : (cert.map Prod.fst).Nodup) :
    ((splitCertificate plan graph cert).map Prod.fst).Nodup := by
  have renamed := List.Nodup.map plan.label.injective unique
  cases found : cert.lookup plan.header with
  | none => simpa [splitCertificate, found, Function.comp_def] using renamed
  | some required =>
    simp only [splitCertificate, found, List.map_cons, List.nodup_cons, List.map_map, Function.comp_def]
    refine ⟨?_, by simpa [Function.comp_def] using renamed⟩
    simp only [List.mem_map, not_exists]
    rintro ⟨key, names⟩ ⟨_, eq⟩
    exact plan.fresh key eq

private theorem forward_checked (edge : plan.hasEdge graph = true) (cert : Certificate V K)
    {required : List V} (found : cert.lookup plan.header = some required)
    {out : Route W J} (member : out ∈ routes (plan.rewrite graph) (some plan.forward)) :
    checkRoute (splitCertificate plan graph cert)
      ((required ++ edgeReads graph plan.predecessor plan.header).map plan.register) out = true := by
  have reads := renamed_edge_reads plan graph plan.predecessor plan.header
  rw [plan.rekey_selected] at reads
  simp only [routes, plan.lookup_forward graph edge, Option.elim_some, Plan.forwardBlock, br,
    bodyRoutes, termRoutes, reads, List.map_cons, List.map_nil, List.mem_singleton] at member
  subst out
  have needed : (edgeReads graph plan.predecessor plan.header).all
      (fun name => (required ++ edgeReads graph plan.predecessor plan.header).contains name) = true :=
    List.all_eq_true.mpr fun _ mem => List.contains_iff_mem.mpr (List.mem_append_right _ mem)
  have carried : required.all
      (fun name => (required ++ edgeReads graph plan.predecessor plan.header).contains name) = true :=
    List.all_eq_true.mpr fun _ mem => List.contains_iff_mem.mpr (List.mem_append_left _ mem)
  simp only [checkRoute, Access.scan, List.append_nil, renamed_reads, needed, carried, ite_true,
    Option.any_some, Option.elim_some, lookup_renamed_claim, found, Option.map_some]

theorem certificate_check (inputs : List V) (cert : Certificate V K)
    (original : check graph inputs cert = true) (edge : plan.hasEdge graph = true)
    (normalized : (plan.rewrite graph).check = true) :
    check (plan.rewrite graph) (inputs.map plan.register) (splitCertificate plan graph cert) = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at original ⊢
  obtain ⟨_, unique, uniqueClaims, entry, blocks⟩ := original
  refine ⟨normalized, ?_, splitCert_unique plan graph cert uniqueClaims, ?_, ?_⟩
  · rw [definitions_renamed]
    exact List.Nodup.map plan.register.injective unique
  · intro route member
    obtain ⟨old, oldMem, related⟩ := routes_match plan graph edge none member
    exact checks_related plan graph cert inputs none related (entry _ oldMem)
  · have checkedOld (claim : K × List V) (mem : claim ∈ cert) :
        ((plan.rewrite graph).blocks.lookup (plan.label claim.1)).isSome = true ∧
          ∀ route ∈ routes (plan.rewrite graph) (some (plan.label claim.1)),
            checkRoute (splitCertificate plan graph cert) (claim.2.map plan.register) route = true := by
      refine ⟨by simpa [plan.lookup_renamed] using (blocks claim mem).1, ?_⟩
      intro route routeMem
      obtain ⟨old, oldMem, related⟩ := routes_match plan graph edge (some claim.1) routeMem
      exact checks_related plan graph cert claim.2 (some claim.1) related ((blocks claim mem).2 _ oldMem)
    intro claim mem
    cases found : cert.lookup plan.header with
    | none =>
      simp only [splitCertificate, found, List.mem_map] at mem
      obtain ⟨old, belongs, rfl⟩ := mem
      exact checkedOld old belongs
    | some required =>
      simp only [splitCertificate, found, List.mem_cons, List.mem_map] at mem
      rcases mem with rfl | ⟨old, belongs, rfl⟩
      · exact ⟨by simp [plan.lookup_forward graph edge], fun route mem =>
          forward_checked plan graph edge cert found mem⟩
      · exact checkedOld old belongs


end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.Arrival
