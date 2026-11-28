module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs.Reindex

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Model Val read)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (tuple_get_map)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin newest weaken)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

universe w

variable {arity : Nat} {past sigs ports : List (List PortTy)} {t : PortTy}

theorem get_pullTuple {F : PortTy → Type w} {source target : List PortTy}
    (rename : ∀ {t}, Port source t → Port target t) (input : Tuple F target) (p : Port source t) :
    (InputPermutation.pullTuple (fun p => rename p) input).get p = input.get (rename p) := by
  induction p with
  | head => rfl
  | tail p ih => exact ih (fun p => rename (.tail p))

private theorem argumentPort_slot {n : Nat} (p : Port (wordPorts n) wordPort) :
    argumentPort n (InputPermutation.slot p) = p := by
  induction n with
  | zero => cases p
  | succ n ih =>
    cases p with
    | head => rfl
    | tail p => exact congrArg Port.tail (ih p)

theorem port_symm (perm : InputPermutation arity) (p : Port (wordPorts arity) t) :
    InputPermutation.port perm.symm (perm.port p) = p := by
  have sameSort := InputPermutation.slotSort p
  subst t
  change argumentPort arity (perm.symm
    (InputPermutation.slot (argumentPort arity (perm (InputPermutation.slot p))))) = p
  rw [InputPermutation.slot_argumentPort, Equiv.symm_apply_apply]
  exact argumentPort_slot p

private theorem tuple_ext {F : PortTy → Type w} {outputs : List PortTy} (xs ys : Tuple F outputs)
    (agree : ∀ {s} (p : Port outputs s), xs.get p = ys.get p) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons head tail ih =>
    cases ys with
    | cons y rest => exact congrArg₂ Tuple.cons (agree .head) (ih rest (fun p => agree (.tail p)))

theorem pull_symm {value : Unit → Type w} (perm : InputPermutation arity)
    (input : Tuple (Val value) (wordPorts arity)) :
    perm.pull (InputPermutation.pull perm.symm input) = input := by
  apply tuple_ext
  intro _ p
  simp only [InputPermutation.pull, InputMap.pull, get_pullTuple]
  exact congrArg input.get (port_symm perm p)

theorem read_mapColumn {F : PortTy → Type w} {source target out : List PortTy}
    (map : ∀ {t}, Port source t → Port target t) (input : Tuple F target)
    (wires : Wires source past out) (locals : Locals F past) :
    (mapColumn (fun p => map p) wires).read input locals =
      wires.read (InputPermutation.pullTuple (fun p => map p) input) locals := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p => exact congrArg₂ Tuple.cons (get_pullTuple (fun p => map p) input p).symm ih
    | output _ _ => exact congrArg (fun tail => Tuple.cons _ tail) ih

theorem pull_comp {middle target : Nat} {value : Unit → Type w}
    (first : InputMap arity middle) (second : InputMap middle target)
    (input : Tuple (Val value) (wordPorts target)) :
    InputMap.pull (second ∘ first) input = first.pull (second.pull input) := by
  apply tuple_ext
  intro sort p
  have sameSort := InputPermutation.slotSort p
  subst sort
  simp only [InputMap.pull, get_pullTuple]
  change input.get (argumentPort target (second (first (InputPermutation.slot p)))) =
    input.get (argumentPort target
      (second (InputPermutation.slot (argumentPort middle (first (InputPermutation.slot p))))))
  rw [InputPermutation.slot_argumentPort]

theorem initial_reindex (p : Plan arity) (perm : InputPermutation arity)
    (m : Model WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (p.reindexInputs perm).graph.initial m input = p.graph.initial m (perm.pull input) :=
  read_mapColumn (fun p => perm.port p) input p.entry PUnit.unit

-- Every header operand names an old bank slot or a producer.
private def Local (wire : Origin (bankArgs arity) past t) : Prop :=
  match wire with
  | .arg port => ∃ old : Port (wordPorts arity) t, port = suffixPort (wordPorts arity) old
  | .output .. => True

private def LocalColumn {outputs : List PortTy} (wires : Wires (bankArgs arity) past outputs) : Prop :=
  ∀ {s} (port : Port outputs s), Local (wires.get port)

private theorem local_nil : LocalColumn (.nil : Wires (bankArgs arity) past []) :=
  fun p => nomatch p

private theorem local_old (port : Port (wordPorts arity) t) :
    Local (.arg (suffixPort (wordPorts arity) port) : Origin (bankArgs arity) past t) :=
  ⟨port, rfl⟩

private theorem local_cons {outputs : List PortTy} {head : Origin (bankArgs arity) past t}
    {rest : Wires (bankArgs arity) past outputs} (h : Local head) (tail : LocalColumn rest) :
    LocalColumn (.cons head rest) := by
  intro _ port
  cases port with
  | head => exact h
  | tail port => exact tail port

private theorem local_weaken (head : List PortTy) {wire : Origin (bankArgs arity) past t}
    (stable : Local wire) : Local (weaken head wire) := by
  cases wire with
  | arg port => exact stable
  | output _ _ => trivial

private theorem local_keep (flow : Dataflow WordOp (bankArgs arity) past sigs)
    {wire : Origin (bankArgs arity) past t} (stable : Local wire) :
    Local (keepOrigin flow wire) := by
  induction flow with
  | nil => exact stable
  | cons op args rest ih => exact ih (local_weaken _ stable)

private theorem local_cast {before after : List (List PortTy)} (eq : before = after)
    {wire : Origin (bankArgs arity) before t} (stable : Local wire) :
    Local (eq ▸ wire : Origin (bankArgs arity) after t) := by
  cases eq
  exact stable

private theorem local_replace {outputs : List PortTy} (value : Origin (bankArgs arity) past t)
    (wires : Wires (bankArgs arity) past outputs) (dst : Port outputs t)
    (valueLocal : Local value) (wiresLocal : LocalColumn wires) :
    LocalColumn (replaceWire value wires dst) := by
  induction dst with
  | head =>
    cases wires with
    | cons _ rest => exact local_cons valueLocal (fun q => wiresLocal (.tail q))
  | tail dst ih =>
    cases wires with
    | cons head rest =>
      exact local_cons (wiresLocal .head) (ih value rest valueLocal (fun q => wiresLocal (.tail q)))

private theorem rowColumn_local (updates : List (FeedbackUpdate arity)) (past : List (List PortTy))
    (wires : Wires (bankArgs arity) past (wordPorts arity)) (stable : LocalColumn wires) :
    LocalColumn (rowColumnAt (argumentPort arity) past updates wires) := by
  induction updates generalizing past with
  | nil => exact stable
  | cons u rest ih =>
    apply ih
    apply local_replace (newest .head) _ _ trivial
    intro _ port
    rw [tuple_get_map]
    exact local_weaken _ (stable port)

private def LocalFlow : {past sigs : List (List PortTy)} →
    Dataflow WordOp (bankArgs arity) past sigs → Prop
  | _, _, .nil => True
  | _, _, .cons _ args rest => LocalColumn args ∧ LocalFlow rest

private theorem local_row (updates : List (FeedbackUpdate arity)) (past : List (List PortTy)) :
    LocalFlow (rowSuffixAt (argumentPort arity) past updates) := by
  induction updates generalizing past with
  | nil => trivial
  | cons u rest ih =>
    exact ⟨local_cons (local_old (argumentPort arity u.left))
      (local_cons (local_old (argumentPort arity u.right)) local_nil), ih _⟩

private theorem local_append (flow : Dataflow WordOp (bankArgs arity) past sigs)
    (tail : Dataflow WordOp (bankArgs arity) (extend past sigs) ports)
    (first : LocalFlow flow) (last : LocalFlow tail) : LocalFlow (appendFlow flow tail) := by
  induction flow with
  | nil => exact last
  | cons op args rest ih => exact ⟨first.1, ih tail first.2 last⟩

private theorem local_setup {producers : Nat} (limit : Silmaril.Machine.Lir.Word)
    (operand : GuardOperand arity producers) :
    LocalFlow (guardSetup (past := past) limit operand) := by
  cases operand with
  | limit => exact ⟨local_nil, trivial⟩
  | bank _ | computed _ => trivial

private theorem local_rhs (p : Plan arity) (operand : GuardOperand arity p.updates.length) :
    Local (guardRhsWire p.producerWire operand) := by
  cases operand with
  | limit | computed _ => trivial
  | bank i => exact local_old (argumentPort arity i)

private theorem local_test (p : Plan arity) : LocalFlow p.test :=
  local_append p.guardSetup _ (local_setup p.limit p.guardOperand)
    ⟨local_cons (local_keep p.guardSetup (wire := p.guardWire) trivial)
      (local_cons (local_rhs p p.guardOperand) local_nil), trivial⟩

private theorem local_feedback (p : Plan arity) : LocalColumn (p.graph.phiInputs .backedge) := by
  have base : LocalColumn (p.copies.map fun _ wire =>
      match wire with
      | .arg slot => Origin.arg (past := []) (suffixPort (wordPorts arity) slot)
      | .output i _ => i.elim0) := by
    intro _ port
    rw [tuple_get_map]
    cases p.copies.get port with
    | arg old => exact ⟨old, rfl⟩
    | output i _ => exact i.elim0
  have row : LocalColumn p.feedbackColumn := rowColumn_local p.updates [] _ base
  intro sort port
  change Local ((p.feedbackColumn.map fun _ wire => joinedOrigin
    (past := []) (sigs := rowSigs p.updates) (tail := p.guardSigs) (keepOrigin p.test wire)).get port)
  rw [tuple_get_map]
  exact local_cast _ (local_keep p.test (row port))

variable (m : Model.{0, 0, w} WordOp)
variable (left right old : Tuple (Val m.value) (wordPorts arity))

private theorem read_local (wire : Origin (bankArgs arity) past t) (stable : Local wire)
    (locals : Locals (Val m.value) past) :
    read m wire (appendTuple old left) locals = read m wire (appendTuple old right) locals := by
  cases wire with
  | arg port =>
    obtain ⟨prior, rfl⟩ := stable
    exact (suffix_get left old prior).trans (suffix_get right old prior).symm
  | output _ _ => rfl

private theorem read_localColumn {outputs : List PortTy} (wires : Wires (bankArgs arity) past outputs)
    (stable : LocalColumn wires) (locals : Locals (Val m.value) past) :
    wires.read (appendTuple old left) locals = wires.read (appendTuple old right) locals := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    exact congrArg₂ Tuple.cons (read_local m left right old wire (stable .head) locals)
      (ih (fun p => stable (.tail p)))

private theorem eval_localFlow (flow : Dataflow WordOp (bankArgs arity) past sigs)
    (stable : LocalFlow flow) (locals : Locals (Val m.value) past) :
    flow.eval m (appendTuple old left) locals = flow.eval m (appendTuple old right) locals := by
  induction flow with
  | nil => rfl
  | cons op args rest ih =>
    simp only [Dataflow.eval, read_localColumn m left right old args stable.1 locals]
    exact ih stable.2 _

theorem step_capture_congr (p : Plan arity) :
    p.graph.step m left old = p.graph.step m right old := by
  let locals := p.graph.header.eval m (appendTuple old right) PUnit.unit
  have sameLocals := eval_localFlow m left right old p.graph.header
    (local_append p.row p.test (local_row p.updates []) (local_test p)) PUnit.unit
  have predLocal : Local p.graph.predicate := local_cast _ (local_cast _ trivial)
  have exitLocal : Local p.exitWire := by
    cases selected : p.exitProducer with
    | none =>
      simpa only [Plan.exitWire, selected, Option.elim] using
        (local_old (past := p.rowPast) (argumentPort arity p.exitSlot))
    | some index =>
      simp only [Plan.exitWire, selected, Option.elim]
      trivial
  have resultLocal : Local p.graph.result := local_cast _ (local_keep p.test exitLocal)
  change _ = locals at sameLocals
  change (if (read m p.graph.predicate (appendTuple old left)
    (p.graph.header.eval m (appendTuple old left) PUnit.unit)).down then
      Sum.inr ((p.graph.phiInputs .backedge).read (appendTuple old left)
        (p.graph.header.eval m (appendTuple old left) PUnit.unit))
    else Sum.inl (read m p.graph.result (appendTuple old left)
      (p.graph.header.eval m (appendTuple old left) PUnit.unit))) = _
  rw [sameLocals, read_local m left right old _ predLocal locals,
    read_local m left right old _ resultLocal locals]
  exact congrArg (fun bank => if (read m p.graph.predicate (appendTuple old right) locals).down
    then Sum.inr bank else Sum.inl (read m p.graph.result (appendTuple old right) locals))
    (read_localColumn m left right old _ (local_feedback p) locals)

theorem step_reindex (p : Plan arity) (perm : InputPermutation arity)
    (input old : Tuple (Val m.value) (wordPorts arity)) :
    (p.reindexInputs perm).graph.step m input old = p.graph.step m (perm.pull input) old :=
  step_capture_congr m input (perm.pull input) old p

theorem denote_reindex (p : Plan arity) (perm : InputPermutation arity)
    (input : Tuple (Val m.value) (wordPorts arity)) :
    (p.reindexInputs perm).program.graph.denote m input =
      p.program.graph.denote m (perm.pull input) := by
  simp only [Plan.program, Graph.denote, initial_reindex, step_reindex]

theorem equation_reindex_holds_iff (left right : Plan arity) (perm : InputPermutation arity) :
    ((left.reindexInputs perm).equation (right.reindexInputs perm)).Holds m ↔
      (left.equation right).Holds m := by
  change (∀ input : Tuple (Val m.value) (wordPorts arity),
    (left.reindexInputs perm).program.graph.denote m input =
      (right.reindexInputs perm).program.graph.denote m input) ↔ _
  simp only [denote_reindex]
  constructor
  · intro holds input
    have observes := holds (InputPermutation.pull perm.symm input)
    rw [pull_symm (value := m.value) perm input] at observes
    exact observes
  · intro holds input
    exact holds (perm.pull input)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs.Reindex
