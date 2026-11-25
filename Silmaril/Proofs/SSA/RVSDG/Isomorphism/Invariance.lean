module

public import Silmaril.SSA.RVSDG.Isomorphism.Defs

public section

namespace Silmaril.SSA.RVSDG.Isomorphism.Proofs

universe u v w

variable {Ty : Type u} {F : Ty → Type w}

-- Retain the type tag when comparing colours at corresponding numeric addresses.
private def colours {ts : Ports Ty} : Tuple F ts → List (Sigma F)
  | .nil => []
  | @Tuple.cons _ _ t _ value rest => ⟨t, value⟩ :: colours rest

private theorem colours_injective {ts : Ports Ty} (left right : Tuple F ts)
    (eq : colours left = colours right) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons val left ih =>
    cases right with
    | cons other right =>
      have head := (List.cons.inj eq).1
      have tail := (List.cons.inj eq).2
      have heads : val = other := by simpa only [Sigma.mk.injEq, true_and, heq_eq_eq] using head
      rw [heads, ih right tail]

private theorem colours_get {ts : Ports Ty} {t : Ty} (tuple : Tuple F ts) (p : Port ts t) :
    (colours tuple)[p.index]? = some ⟨t, tuple.get p⟩ := by
  induction p with
  | head => cases tuple; rfl
  | tail p ih => cases tuple with | cons _ rest => exact ih rest

private def store {past : List (Ports Ty)} : Locals F past → List (List (Sigma F)) :=
  match past with
  | [] => fun _ => []
  | _ :: _ => fun values => colours values.1 :: store values.2

private theorem store_length {past : List (Ports Ty)} (values : Locals F past) :
    (store values).length = past.length := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ (ih values.2)

private theorem store_snoc {past : List (Ports Ty)} (values : Locals F past)
    {ts : Ports Ty} (next : Tuple F ts) :
    store (values.snoc next) = store values ++ [colours next] := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact congrArg (colours values.1 :: ·) (ih values.2)

private theorem store_get {past : List (Ports Ty)} (values : Locals F past) (i : Fin past.length) :
    (store values)[i.val]? = some (colours (values.get i)) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih values.2 j

private theorem prefix_get {α : Type w} {before all : List α} (h : before <+: all)
    {i : Nat} (bound : i < before.length) : all[i]? = before[i]? := by
  obtain ⟨rest, rfl⟩ := h
  exact List.getElem?_append_left bound

private theorem source_before {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) {vertex port : Nat}
    (mem : Address.output vertex port ∈ wires.addresses) : vertex < past.length := by
  induction wires with
  | nil => cases mem
  | cons origin tail ih =>
    rcases List.mem_cons.mp mem with atHead | inTail
    · cases origin with
      | arg p => cases atHead
      | output i p =>
        have eq : vertex = i.val := (Address.output.inj atHead).1
        exact eq ▸ i.isLt
    · exact ih inTail

private def lookup (entry : List (Sigma F)) (all : List (List (Sigma F))) : Address → Option (Sigma F)
  | .arg p => entry[p]?
  | .output i p => (all[i]?).bind (fun ports => ports[p]?)

private theorem read_colours {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) (values : Locals F past)
    (all : List (List (Sigma F))) (pref : store values <+: all) :
    (colours (wires.read entry values)).map some = wires.addresses.map (lookup (colours entry) all) := by
  induction wires with
  | nil => rfl
  | cons origin tail ih =>
    simp only [Wires.read, Tuple.map, colours, List.map_cons, Wires.addresses]
    congr 1
    cases origin with
    | arg p => exact (colours_get entry p).symm
    | output i p =>
      have bound : i.val < (store values).length := by rw [store_length]; exact i.isLt
      simp only [Origin.address, lookup, prefix_get pref bound, store_get, Option.bind_some,
        colours_get]

private theorem compare_reads {args args' ins ins' : Ports Ty}
    {past past' : List (Ports Ty)} (left : Wires args past ins) (right : Wires args' past' ins')
    (entry : Tuple F args) (entry' : Tuple F args') (inputs : colours entry = colours entry')
    (values : Locals F past) (values' : Locals F past')
    {all all' : List (List (Sigma F))} (pref : store values <+: all) (pref' : store values' <+: all')
    (rename : Nat → Nat) (wires : left.addresses.map (Address.rename rename) = right.addresses)
    (sources : ∀ i p, Address.output i p ∈ left.addresses → all[i]? = all'[rename i]?) :
    colours (left.read entry values) = colours (right.read entry' values') := by
  apply (List.map_inj_right (f := some) (fun _ _ => Option.some.inj)).1
  rw [read_colours left entry values all pref, read_colours right entry' values' all' pref',
    ← wires, List.map_map]
  apply List.map_congr_left
  intro addr present
  cases addr with
  | arg p => exact congrArg (·[p]?) inputs
  | output i p =>
    exact congrArg (fun out : Option (List (Sigma F)) => out.bind (fun ports => ports[p]?))
      (sources i p present)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private abbrev Runners (m : Model.{u, v, w} Op) (nodes : Nodes Op args past sigs) :=
  (i : Fin sigs.length) → Fin (nodes i).shape.regionCount →
    Tuple m.Val (nodes i).shape.entry → Tuple m.Val (nodes i).shape.exit

/-- The numbered evaluator's full local store, before reading the result wires. -/
private def trace (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) :
    (past sigs : List (Ports (PortType V S))) → Locals m.Val past →
    (nodes : Nodes Op args past sigs) → Runners m nodes → Locals m.Val (extend past sigs)
  | _, [], values, _, _ => values
  | past, head :: rest, values, nodes, children =>
    let node := nodes 0
    let output := node.shape.eval m (children 0) (node.inputs.read entry values)
    trace m entry (past ++ [head]) rest (values.snoc output)
      (fun i => nodes i.succ) (fun i => children i.succ)

private theorem trace_result (m : Model.{u, v, w} Op) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (values : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes)
    (results : Wires args (extend past sigs) outs) :
    evalTable m entry past sigs values nodes children results =
      results.read entry (trace m entry past sigs values nodes children) := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    simp only [evalTable, trace]
    apply ih

private theorem trace_prefix (m : Model.{u, v, w} Op) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (values : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes) :
    store values <+: store (trace m entry past sigs values nodes children) := by
  induction sigs generalizing past with
  | nil => exact ⟨[], List.append_nil _⟩
  | cons head tail ih =>
    simp only [trace]
    apply List.IsPrefix.trans _ (ih _ _ _ _)
    exact ⟨_, (store_snoc _ _).symm⟩

private theorem trace_at (m : Model.{u, v, w} Op) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (values : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes) (i : Fin sigs.length) :
    let all := store (trace m entry past sigs values nodes children)
    let node := nodes i
    ∃ before : Locals m.Val (site past sigs i).1,
      store before <+: all ∧
      all[(site past sigs i).1.length]? =
        some (colours (node.shape.eval m (children i) (node.inputs.read entry before))) := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    let first := (nodes 0).shape.eval m (children 0) ((nodes 0).inputs.read entry values)
    let next := values.snoc first
    let later := trace m entry (past ++ [head]) tail next
      (fun j => nodes j.succ) (fun j => children j.succ)
    have preserves : store next <+: store later := trace_prefix m entry _ _ _ _ _
    refine Fin.cases ?_ (fun j => ?_) i
    · have addsFirst : store values <+: store next := ⟨[colours first], (store_snoc values first).symm⟩
      refine ⟨values, addsFirst.trans preserves, ?_⟩
      change (store later)[past.length]? = some (colours first)
      have bound : past.length < (store next).length := by
        rw [store_length, List.length_append]
        simp
      rw [prefix_get preserves bound, store_snoc, List.getElem?_append_right (by simp only [store_length, Nat.le_refl]),
        store_length, Nat.sub_self]
      rfl
    · exact ih (past ++ [head]) next _ _ j

private theorem site_length (past sigs : List (Ports Ty)) (i : Fin sigs.length) :
    (site past sigs i).1.length = past.length + i.val := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (site (past ++ [head]) tail j).1.length = past.length + (j.val + 1)
      rw [ih, List.length_append, Nat.add_assoc, Nat.add_comm [_].length]
      rfl

private def graphTrace (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (entry : Tuple m.Val args) : Locals m.Val (extend [] sigs) :=
  trace m entry [] sigs PUnit.unit graph.nodes (fun i j input => (graph.children i j).run m input)

private theorem graphTrace_result (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (entry : Tuple m.Val args) :
    graph.run m entry = graph.results.read entry (graphTrace m graph entry) := by
  cases graph with
  | region nodes children results => exact trace_result m entry [] sigs PUnit.unit nodes _ results

private theorem graphTrace_at (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (entry : Tuple m.Val args) (i : Fin sigs.length) :
    let all := store (graphTrace m graph entry)
    let node := graph.nodes i
    ∃ before : Locals m.Val (site [] sigs i).1,
      store before <+: all ∧
      all[i.val]? = some (colours (node.shape.eval m
        (fun arm input => (graph.children i arm).run m input) (node.inputs.read entry before))) := by
  simpa only [graphTrace, site_length, List.length_nil, Nat.zero_add] using
    trace_at m entry [] sigs PUnit.unit graph.nodes
      (fun i arm input => (graph.children i arm).run m input) i

private theorem extend_length (past sigs : List (Ports Ty)) :
    (extend past sigs).length = past.length + sigs.length := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    change (extend (past ++ [head]) tail).length = past.length + (tail.length + 1)
    rw [ih, List.length_append, Nat.add_assoc, Nat.add_comm [_].length]
    rfl

private theorem compare_label (m : Model.{u, v, w} Op) {left right : NodeLabel Op}
    (same : left = right)
    (runLeft : Fin left.arity → Tuple m.Val left.shape.entry → Tuple m.Val left.shape.exit)
    (runRight : Fin right.arity → Tuple m.Val right.shape.entry → Tuple m.Val right.shape.exit)
    (input : Tuple m.Val left.ins) (input' : Tuple m.Val right.ins)
    (equalInputs : colours input = colours input')
    (children : ∀ arm arg arg', colours arg = colours arg' →
      colours (runLeft arm arg) = colours (runRight (Fin.cast (congrArg NodeLabel.arity same) arm) arg')) :
    colours (left.shape.eval m runLeft input) = colours (right.shape.eval m runRight input') := by
  subst right
  have equal := colours_injective input input' equalInputs
  subst input'
  obtain ⟨ins, outs, shape⟩ := left
  cases shape with
  | simple opcode => rfl
  | gamma extra =>
    cases input with
    | cons choice entry => exact children choice.down entry entry rfl

private theorem run_colours {argsL argsR outsL outsR : Ports (PortType V S)}
    {sigsL sigsR : List (Ports (PortType V S))}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op)
    (inputL : Tuple m.Val argsL) (inputR : Tuple m.Val argsR)
    (inputEq : colours inputL = colours inputR) :
    colours (left.run m inputL) = colours (right.run m inputR) := by
  induction iso with
  | @intro argsL argsR outsL outsR sigsL sigsR left right _ _ ids labels inputs results _ childIH =>
    let allL := store (graphTrace m left inputL)
    let allR := store (graphTrace m right inputR)
    have vertices (n : Nat) (valid : n < sigsL.length) :
        allL[n]? = allR[renameVertex ids n]? := by
      induction n using Nat.strongRecOn with
      | ind n earlier =>
        let i : Fin sigsL.length := ⟨n, valid⟩
        obtain ⟨beforeL, prefL, atL⟩ := graphTrace_at m left inputL i
        obtain ⟨beforeR, prefR, atR⟩ := graphTrace_at m right inputR (ids i)
        simp only [renameVertex, dite_eq_left valid]
        change allL[i.val]? = allR[(ids i).val]?
        rw [atL, atR]
        apply congrArg some
        refine compare_label m (labels i) _ _ _ _ ?_ (childIH i)
        apply compare_reads _ _ inputL inputR inputEq beforeL beforeR prefL prefR _ (inputs i)
        intro producer port mem
        have earlierProducer : producer < n := by
          simpa only [site_length, List.length_nil, Nat.zero_add, i] using
            source_before (left.nodes i).inputs mem
        exact earlier producer earlierProducer (Nat.lt_trans earlierProducer valid)
    rw [graphTrace_result, graphTrace_result]
    refine compare_reads left.results right.results inputL inputR inputEq _ _
      ⟨[], List.append_nil _⟩ ⟨[], List.append_nil _⟩ _ results ?_
    intro producer port mem
    apply vertices
    simpa only [extend_length, List.length_nil, Nat.zero_add] using source_before left.results mem

theorem run_eq {sigs' : List (Ports (PortType V S))}
    {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) :
    left.run m entry = right.run m entry :=
  colours_injective _ _ (run_colours iso m entry entry rfl)

end Silmaril.SSA.RVSDG.Isomorphism.Proofs
