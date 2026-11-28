module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Signature Ty ValueSort dataPorts)
open GVN (Producer keepOrigin newest newestIndex olderIndex weaken)
open GVN.Cyclic
open GVN.Cyclic.Builder
open Activation (HeaderWire Site headerInput headerLatch inputSlot operandWires sourceWire)
open Silmaril.SSA.RVSDG (Origin Port Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out t : ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}

section Enumeration

private theorem older_val {T : Type u} (head : List T) :
    (scope : List (List T)) → (i : Fin scope.length) → (olderIndex head scope i).val = i.val
  | [], i => i.elim0
  | first :: tail, i =>
    Fin.cases (motive := fun j => (olderIndex head (first :: tail) j).val = j.val)
      rfl (fun j => congrArg Nat.succ (older_val head tail j)) i

private theorem newest_val {T : Type u} (head : List T) :
    (scope : List (List T)) → (newestIndex head scope).val = scope.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (newest_val head tail)

/-- Bounds on real producer addresses ignore reads of fixed arguments. -/
private def Before {T : Type u} {args : List T} {past : List (List T)} {t : T}
    (cut : Nat) (wire : Origin args past t) : Prop :=
  ∀ node, wire.producer = some node → node < cut

variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {flow : Dataflow Op args past sigs}

private theorem weaken_producer {ty : Ty Data} (head : List (Ty Data)) (wire : Origin args past ty) :
    (weaken head wire).producer = wire.producer := by
  cases wire with
  | arg => rfl
  | output i _ => exact congrArg some (older_val head past i)

private theorem keep_producer {ty : Ty Data} (flow : Dataflow Op args past sigs) (wire : Origin args past ty) :
    (keepOrigin flow wire).producer = wire.producer := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => exact (ih (weaken _ wire)).trans (weaken_producer _ wire)

private theorem extend_append {T : Type u} (past sigs : List (List T)) :
    extend past sigs = past ++ sigs := by
  induction sigs generalizing past with
  | nil => simp [extend]
  | cons _ _ ih => simp [extend, ih, List.append_assoc]

private theorem producers_length (flow : Dataflow Op args past sigs) :
    (Pass.producers flow).length = sigs.length := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => simp [Pass.producers, ih]

private theorem get_map {T : Type u} {F : T → Type v} {G : T → Type w} {args : List T} {ty : T}
    (p : Port args ty) (tuple : Tuple F args) (f : ∀ ty, F ty → G ty) :
    (tuple.map f).get p = f _ (tuple.get p) := by
  induction p with
  | head => cases tuple; rfl
  | tail _ ih => cases tuple with | cons _ tail => exact ih tail

private theorem producer_at (flow : Dataflow Op args past sigs)
    (i : Fin (Pass.producers flow).length) :
    let ref := (Pass.producers flow).get i
    let j : Fin sigs.length := ⟨i.val, producers_length flow ▸ i.isLt⟩
    sigs[j] = [.value ref.1] ∧ ref.2.origin.producer = some (past.length + i.val) ∧
      ∀ {s} (p : Port (dataPorts ref.2.key.ins) s), Before (past.length + i.val) (ref.2.key.operands.get p) := by
  induction flow with
  | nil => exact i.elim0
  | @cons scope sigs ins result op operands rest ih =>
    change Fin (((Pass.producers rest).map
      (fun (item : Σ sort, Producer rest sort) => (⟨item.1, .later item.2⟩ :
        Σ sort, Producer (.cons op operands rest) sort))).length + 1) at i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨rfl, ?_, ?_⟩
      · exact (keep_producer rest (newest .head)).trans (congrArg some (newest_val [.value result] scope))
      · intro s p node origin
        change Port (dataPorts ins) s at p
        change ((operands.map fun _ wire => keepOrigin rest (weaken [.value result] wire)).get p).producer = _ at origin
        rw [get_map, keep_producer, weaken_producer] at origin
        cases actual : operands.get p with
        | arg => simp [actual, Origin.producer] at origin
        | output index port =>
          have same : index.val = node := by simpa [actual, Origin.producer] using origin
          exact same ▸ index.isLt
    · have inTail : j.val < (Pass.producers rest).length := by simpa only [List.length_map] using j.isLt
      have facts := ih ⟨j.val, inTail⟩
      dsimp only at facts ⊢
      have cut : (scope ++ [[(.value result : Ty Data)]]).length + j.val = scope.length + (j.val + 1) := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [cut] at facts
      let ref := (Pass.producers rest).get ⟨j.val, inTail⟩
      have fetched : (Pass.producers (.cons op operands rest)).get j.succ =
          ⟨ref.1, Producer.later ref.2⟩ := by
        change (List.map _ (Pass.producers rest))[j.val] = _
        rw [List.getElem_map]
        change (match ref with
          | ⟨sort, producer⟩ =>
            (⟨sort, Producer.later producer⟩ : Σ sort, Producer (.cons op operands rest) sort)) = _
        cases ref
        rfl
      rw [fetched]
      exact facts

private theorem latch_mem (port : Port (dataPorts carried) (.value t)) :
    (⟨t, port⟩ : Σ s, Port (dataPorts carried) (.value s)) ∈ Pass.operandPorts carried := by
  induction carried with
  | nil => cases port
  | cons head tail ih =>
    cases port with
    | head => exact List.mem_cons_self
    | tail inner =>
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨t, inner⟩, ih inner, rfl⟩)

private theorem header_arg_cases (port : Port (Loop.headerPorts inputs carried) (.value t)) :
    (∃ entry : Port inputs t, port = headerInput (dataPorts carried) entry) ∨
      ∃ latch : Port (dataPorts carried) (.value t), port = headerLatch latch (dataPorts inputs) := by
  induction inputs with
  | nil => exact .inr ⟨port, rfl⟩
  | cons head rest ih =>
    cases port with
    | head => exact .inl ⟨.head, rfl⟩
    | tail port =>
      rcases ih port with ⟨entry, rfl⟩ | ⟨latch, rfl⟩
      · exact .inl ⟨.tail entry, rfl⟩
      · exact .inr ⟨latch, rfl⟩



private theorem location_origin_of_eq {left right : Σ s, Location loop s} (eq : left = right) :
    (congrArg Sigma.fst eq ▸ left.2.origin) = right.2.origin := by
  subst right
  rfl

private theorem source_of_location (loc : Location loop t)
    (member : (⟨t, loc⟩ : Σ s, Location loop s) ∈ locations loop) :
    ∃ source : Source inputs (sorts loop) t, sourceOrigin loop source = loc.origin := by
  obtain ⟨i, found⟩ := List.get_of_mem member
  exact ⟨.producer i (congrArg Sigma.fst found), location_origin_of_eq found⟩

private theorem singleton_port {ports : List (Ty Data)} {s : ValueSort Data}
    (port : Port ports (.value t)) (shape : ports = [.value s]) :
    s = t ∧ port.index = 0 := by
  subst ports
  cases port with
  | head => exact ⟨rfl, rfl⟩
  | tail inner => cases inner

private theorem output_facts {flow : Dataflow Op args [] sigs} {j : Nat}
    (wire : Origin args (extend [] sigs) (.value t))
    (atIndex : wire.producer = some j)
    (i : Fin (Pass.producers flow).length) (same : i.val = j) :
    ((Pass.producers flow).get i).1 = t ∧ wire.address = .output j 0 := by
  obtain ⟨shape, _, _⟩ := producer_at flow i
  cases wire with
  | arg => cases atIndex
  | output index port =>
    have indexEq : index.val = i.val := (Option.some.inj atIndex).trans same.symm
    have eq : (extend [] sigs)[index] = sigs[i.val]'(producers_length flow ▸ i.isLt) := by
      have atSig : (extend [] sigs)[index] = sigs[index.val]'(by simpa [extend_append] using index.isLt) :=
        List.getElem_of_eq (by simp [extend_append]) _
      simpa only [indexEq] using atSig
    obtain ⟨typed, first⟩ := singleton_port port (eq.trans shape)
    exact ⟨typed, congrArg₂ Silmaril.SSA.RVSDG.Address.output (indexEq.trans same) first⟩

private theorem output_source (wire : HeaderWire inputs carried headerSigs t) {j : Nat}
    (isOutput : wire.producer = some j) :
    ∃ source : Source inputs (sorts loop) t, sourceOrigin loop source = wire := by
  have inScope : j < (Pass.producers loop.header).length := by
    rw [producers_length]
    cases wire with
    | arg => cases isOutput
    | output index port =>
      rw [← Option.some.inj isOutput]
      simpa [extend_append] using index.isLt
  let i : Fin (Pass.producers loop.header).length := ⟨j, inScope⟩
  let ref := (Pass.producers loop.header).get i
  have actualIndex : ref.2.origin.producer = some j := by
    simpa only [ref, List.length_nil, Nat.zero_add, i] using (producer_at loop.header i).2.1
  obtain ⟨typed, actualAddr⟩ := output_facts (flow := loop.header) wire isOutput i rfl
  have refAddr := (output_facts (flow := loop.header) ref.2.origin actualIndex i rfl).2
  have member : (⟨ref.1, .pure ref.2⟩ : Σ sort, Location loop sort) ∈ locations loop :=
    List.mem_append_right _ (List.mem_map.mpr ⟨ref, List.get_mem _ i, rfl⟩)
  obtain ⟨source, eq⟩ := source_of_location (.pure ref.2) member
  subst t
  exact ⟨source, eq.trans (origin_eq _ _ (refAddr.trans actualAddr.symm))⟩

private theorem source_exists (wire : HeaderWire inputs carried headerSigs t) :
    ∃ source : Source inputs (sorts loop) t, sourceOrigin loop source = wire := by
  cases wire with
  | arg port =>
    rcases header_arg_cases port with ⟨entry, rfl⟩ | ⟨latch, rfl⟩
    · exact ⟨.argument entry, rfl⟩
    · exact source_of_location (.phi latch)
        (List.mem_append_left _ (List.mem_map.mpr ⟨⟨t, latch⟩, latch_mem latch, rfl⟩))
  | output i port => exact output_source (.output i port) rfl

private theorem producer_mem {s : ValueSort Data} (ref : Producer flow s) :
    (⟨s, ref⟩ : Σ s, Producer flow s) ∈ Pass.producers flow := by
  induction ref with
  | here => exact List.mem_cons_self
  | later next ih => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨_, next⟩, ih, rfl⟩)

private theorem producer_before (ref : Producer loop.header t) :
    ∃ node, ref.origin.producer = some node ∧
      ∀ {s} (p : Port (dataPorts ref.key.ins) s), Before node (ref.key.operands.get p) := by
  obtain ⟨i, found⟩ := List.get_of_mem (producer_mem ref)
  have facts := (producer_at loop.header i).2
  generalize (Pass.producers loop.header).get i = selected at found facts
  cases found
  exact ⟨0 + i.val, facts.1, facts.2⟩

private def locationProducer (selected : Σ s, Location loop s) : Option Nat :=
  selected.2.origin.producer

/-- Latches occupy the first block of vertex numbers. Each remaining
vertex denotes the producer at its offset in the actual header. -/
private theorem location_number (i : Vertex loop) :
    (location loop i).origin.producer =
      if i.val < (Pass.operandPorts carried).length then none
      else some (i.val - (Pass.operandPorts carried).length) := by
  change locationProducer (loop := loop) ((locations loop)[i.val]'i.isLt) = _
  by_cases latch : i.val < (Pass.operandPorts carried).length
  · rw [ite_eq_left latch]
    have inLatches : i.val < ((Pass.operandPorts carried).map
        (fun (value : Σ s, Port (dataPorts carried) (.value s)) =>
          (⟨value.1, .phi value.2⟩ : Σ s, Location loop s))).length :=
      by simpa only [List.length_map] using latch
    simp only [locations, List.getElem_append_left inLatches, List.getElem_map]
    rfl
  · rw [ite_eq_right latch]
    let count := (Pass.operandPorts carried).length
    have pastLatches : ((Pass.operandPorts carried).map
        (fun (value : Σ s, Port (dataPorts carried) (.value s)) =>
          (⟨value.1, .phi value.2⟩ : Σ s, Location loop s))).length ≤ i.val := by
      simpa only [List.length_map] using Nat.le_of_not_gt latch
    have lengthEq : (locations loop).length = count + (Pass.producers loop.header).length := by
      simp only [locations, List.length_append, List.length_map, count]
    have inProducers : i.val - count < (Pass.producers loop.header).length := by
      have bound : i.val < count + (Pass.producers loop.header).length := by
        simpa only [lengthEq] using i.isLt
      change ¬ i.val < count at latch
      omega
    have facts := (producer_at loop.header ⟨i.val - count, inProducers⟩).2.1
    simp only [locations, List.getElem_append_right pastLatches, List.getElem_map, List.length_map]
    simp only [List.get_eq_getElem, List.length_nil, Nat.zero_add] at facts
    change ((match (Pass.producers loop.header)[i.val - count]'inProducers with
      | ⟨sort, ref⟩ => (⟨sort, .pure ref⟩ : Σ s, Location loop s)) |> locationProducer) = _
    generalize (Pass.producers loop.header)[i.val - count]'inProducers = selected at facts ⊢
    cases selected
    exact facts

private theorem source_producer (j : Vertex loop) (same : sorts loop j = t) :
    (sourceOrigin loop (.producer j same)).producer = (location loop j).origin.producer := by
  change ((same ▸ (location loop j).origin) : HeaderWire inputs carried headerSigs t).producer = _
  cases same
  rfl

end Enumeration

section Decode

variable [DecidableEq (ValueSort Data)]

private theorem argument_mem (port : Port inputs t) : port ∈ argumentPorts t inputs := by
  induction inputs with
  | nil => cases port
  | cons s tail ih =>
    cases port with
    | head => simp [argumentPorts]
    | tail p =>
      by_cases same : s = t
      · subst s
        simp only [argumentPorts]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, ih p, rfl⟩)
      · simp only [argumentPorts, dite_eq_right same]
        exact List.mem_map.mpr ⟨p, ih p, rfl⟩

private theorem entry_decodes (wire : EntryWire inputs entrySigs t) (port : Port inputs t)
    (direct : wire = .arg (inputSlot port)) :
    ∃ checked, decodeEntry? wire = some checked := by
  subst wire
  apply Option.isSome_iff_exists.mp
  unfold decodeEntry?
  apply List.findSome?_isSome_iff.mpr
  exact ⟨port, argument_mem port, by simp⟩

private theorem source_mem (source : Source inputs (sorts loop) t) :
    source ∈ (argumentPorts t inputs).map Source.argument ++
      (List.finRange (locations loop).length).filterMap
        (fun i => if same : sorts loop i = t then some (Source.producer i same) else none) := by
  cases source with
  | argument port =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨port, argument_mem port, rfl⟩)
  | producer i same =>
    apply List.mem_append_right _ (List.mem_filterMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
    simp only [dite_eq_left same]

private theorem header_decodes (wire : HeaderWire inputs carried headerSigs t) :
    ∃ checked, decodeHeader? loop wire = some checked := by
  obtain ⟨source, eq⟩ := source_exists (loop := loop) wire
  apply Option.isSome_iff_exists.mp
  unfold decodeHeader?
  exact List.findSome?_isSome_iff.mpr ⟨source, source_mem source, by simp only [dite_eq_left (congrArg Origin.address eq), Option.isSome_some]⟩

private theorem operands_decode {ins : List (ValueSort Data)}
    (wires : Wires (Loop.headerPorts inputs carried) (extend [] headerSigs) (dataPorts ins)) :
    ∃ checked, decodeOperands? loop wires = some checked := by
  induction ins with
  | nil => cases wires; exact ⟨_, rfl⟩
  | cons _ _ ih =>
    cases wires with
    | cons head tail =>
      obtain ⟨first, decodedHead⟩ := header_decodes (loop := loop) head
      obtain ⟨rest, decodedTail⟩ := ih tail
      simp only [decodeOperands?, decodedHead, decodedTail]
      exact ⟨_, rfl⟩

private theorem site_decodes (direct : ∀ {s} (p : Port (dataPorts carried) (.value s)),
      ∃ entry : Port inputs s, (loop.phiInputs .entry).get p = .arg (inputSlot entry))
    (loc : Location loop t) : ∃ checked, decodeSite? loop loc = some checked := by
  cases loc with
  | phi port =>
    obtain ⟨entry, entryEq⟩ := direct port
    obtain ⟨checkedEntry, decodedEntry⟩ := entry_decodes _ entry entryEq
    obtain ⟨checkedFeedback, decodedFeedback⟩ := header_decodes (loop := loop) ((loop.phiInputs .backedge).get port)
    simp only [decodeSite?, decodedEntry, Option.bind_some, decodedFeedback, Option.map_some]
    exact ⟨_, rfl⟩
  | pure producer =>
    obtain ⟨checkedOperands, decodedOperands⟩ := operands_decode (loop := loop) producer.key.operands
    simp only [decodeSite?, decodedOperands, Option.map_some]
    exact ⟨_, rfl⟩

end Decode

section Order

private theorem operandWire_get {ins : List (ValueSort Data)} (sites : Sites loop)
    (operands : Tuple (Source inputs (sorts loop)) ins) (port : Port ins t) :
    (operandWires sites operands).get (inputSlot port) = sourceWire sites (operands.get port) := by
  induction port with
  | head => cases operands; rfl
  | tail _ ih => cases operands with | cons _ rest => exact ih rest

private theorem all_ordered {ins : List (ValueSort Data)} (i : Vertex loop)
    (operands : Tuple (Source inputs (sorts loop)) ins)
    (each : ∀ {s} (port : Port ins s), Address.precedes i (operands.get port).address = true) :
    (Source.addresses operands).all (Address.precedes i) = true := by
  induction operands with
  | nil => rfl
  | cons head _ ih =>
    have first : Address.precedes i head.address = true := each .head
    simp only [Source.addresses, List.all_cons, first, Bool.true_and]
    exact ih (fun port => each (.tail port))

private theorem pure_order (sites : Sites loop) (origins : Matches sites) (i : Vertex loop)
    (ref : Producer loop.header t) (atSite : (location loop i).origin.producer = ref.origin.producer)
    (operands : Tuple (Source inputs (sorts loop)) ref.key.ins)
    (sameWires : operandWires sites operands = ref.key.operands) :
    (Source.addresses operands).all (Address.precedes i) = true := by
  obtain ⟨consumer, consumerIndex, earlier⟩ := producer_before ref
  have iIndex := atSite.trans consumerIndex
  rw [location_number] at iIndex
  split at iIndex
  · contradiction
  · rename_i notLatch
    have consumerEq := Option.some.inj iIndex
    apply all_ordered i operands
    intro s port
    have readEq : ref.key.operands.get (inputSlot port) = sourceOrigin loop (operands.get port) := by
      rw [← sameWires, operandWire_get, sourceWire_eq sites origins]
    generalize operands.get port = source at readEq ⊢
    cases source with
    | argument => rfl
    | producer j typed =>
      change decide (j < i) = true
      apply decide_eq_true
      change j.val < i.val
      by_cases latch : j.val < (Pass.operandPorts carried).length
      · omega
      · have indexed := source_producer j typed
        rw [location_number, ite_eq_right latch] at indexed
        have bounded := earlier (inputSlot port) _ ((congrArg Origin.producer readEq).trans indexed)
        omega

variable [DecidableEq (ValueSort Data)]

private theorem decoded_order (sites : Sites loop) (origins : Matches sites) (i : Vertex loop)
    (loc : Location loop (sorts loop i)) (same : location loop i = loc)
    (checked : CheckedSite loc) (decoded : decodeSite? loop loc = some checked) :
    (if checked.1.node.isPure then checked.1.node.addresses.all (Address.precedes i) else true) = true := by
  cases loc with
  | phi port =>
    obtain ⟨entry, _, next⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨backedge, _, rfl⟩ := Option.map_eq_some_iff.mp next
    rfl
  | pure producer =>
    obtain ⟨operands, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
    exact pure_order sites origins i producer (congrArg (fun loc => loc.origin.producer) same) operands.1
      (operands.2 sites origins)

private theorem collect_present {k : Nat} {F : Fin k → Type w} (choices : (i : Fin k) → Option (F i))
    (present : ∀ i, ∃ value, choices i = some value) :
    ∃ selected, collectSites choices = some selected ∧ ∀ i, choices i = some (selected i) := by
  induction k with
  | zero => exact ⟨fun i => i.elim0, rfl, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨head, headEq⟩ := present 0
    obtain ⟨tail, tailEq, selectedTail⟩ := ih (fun i => choices i.succ) (fun i => present i.succ)
    refine ⟨Fin.cases head tail, ?_, ?_⟩
    · change (choices 0).bind (fun first =>
        (collectSites fun i => choices i.succ).map (fun rest i => Fin.cases (motive := F) first rest i)) = _
      simp only [headEq, tailEq, Option.bind_some, Option.map_some]
    · exact fun i => Fin.cases (motive := fun j => choices j = some (Fin.cases head tail j)) headEq selectedTail i

theorem build_succeeds
    (direct : ∀ {s} (p : Port (dataPorts carried) (.value s)),
      ∃ entry : Port inputs s, (loop.phiInputs .entry).get p = .arg (inputSlot entry)) :
    ∃ built, build? loop = some built := by
  obtain ⟨decoded, collected, selected⟩ := collect_present _ (fun i => site_decodes direct (location loop i))
  let sites : Sites loop := fun i => (decoded i).1
  have origins : Matches sites := fun i => (decoded i).2.1
  have ordered : checkOrder sites = true :=
    List.all_eq_true.mpr fun i _ => decoded_order sites origins i (location loop i) rfl (decoded i) (selected i)
  change checkOrder (fun i => (decoded i).1) = true at ordered
  obtain ⟨guard, guardEq⟩ := header_decodes (loop := loop) loop.predicate
  obtain ⟨result, resultEq⟩ := header_decodes (loop := loop) loop.result
  unfold build?
  rw [collected]
  simp only [Option.bind_some, dite_eq_left ordered, guardEq, resultEq, Option.map_some]
  exact ⟨_, rfl⟩

end Order

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder
