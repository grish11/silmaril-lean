module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Defs
import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms

/-! Admit the existing emitted activation with its actual post-tail return wires. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Admission

open RVSDG (Origin Port Tuple Wires)
open RVSDG.NestedTheta (identityPorts)
open RVSDG.NestedTheta.ExplicitRuntime (Checked EntryChecked)
open RVSDG.OrderedRuntime.Structured
  (Data Instruction Threaded runtime runtimePort withRuntime splitRuntime append_split
    newestIndex newestPort nextRuntime)
open Memory.Diamond.Institution (PortMap)

variable {args entry outs : List ValueSort}

set_option backward.isDefEq.respectTransparency false

private theorem get_map {T : Type} {F G : T → Type} (map : ∀ t, F t → G t)
    {sorts : List T} (wires : Tuple F sorts) {s : T} (port : Port sorts s) :
    (wires.map map).get port = map s (wires.get port) := by
  induction port with
  | head => cases wires; rfl
  | tail _ ih => cases wires with | cons _ tail => exact ih tail

private theorem identity_get {T : Type} {sorts : List T} {s : T} (port : Port sorts s) :
    (identityPorts sorts).get port = port := by
  induction port with
  | head => rfl
  | tail _ ih => simp only [identityPorts, Tuple.get, get_map, ih]

private theorem splitRuntime_get {F : RVSDG.OrderedRuntime.Structured.Ty ValueSort → Type} (outs : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))
    (xs : Tuple F (Threaded outs)) :
    (splitRuntime outs xs).2 = xs.get (runtimePort outs) := by
  induction outs with
  | nil => cases xs with | cons _ tail => cases tail; rfl
  | cons _ _ ih => cases xs with | cons _ tail => exact ih tail

private theorem route_get_heap (graph : Graph args) {F : RVSDG.OrderedRuntime.Structured.Ty ValueSort → Type} (xs : Tuple F (Petri.Packet args)) :
    (Petri.route graph xs).get (runtimePort (tagged (activationArgs args))) =
      xs.get (runtimePort (tagged (activationArgs args))) := by
  cases xs with
  | cons tag tail =>
    cases tail with
    | cons first tail =>
      cases tail with
      | cons second rest => rfl

private def dataWires {outer : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)} {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))} :
    (sorts : List ValueSort) →
    (∀ {t}, Port (carrier sorts) t → Origin outer past t) → Wires outer past (dataPorts sorts)
  | [], _ => .nil
  | _ :: rest, wire => .cons (wire .head) (dataWires rest (fun p => wire (.tail p)))

private theorem arguments_withRuntime {outer : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)} {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    (live : Origin outer past runtime) (sorts : List ValueSort)
    (wire : ∀ {t}, Port (carrier sorts) t → Origin outer past t) :
    inputsWithHeap live sorts wire = withRuntime live (dataWires sorts wire) := by
  induction sorts with
  | nil => rfl
  | cons _ _ ih => simp only [inputsWithHeap, dataWires, withRuntime, ih]

private theorem ofBase_primitive {a ins out r : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
    {past sigs : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    (live : Origin a past runtime) (i : Data ins) (o : Data out)
    (op : Instruction TailTest Effect ins out) (wires : Wires a past ins)
    (rest : RVSDG.Term ThetaOpcode a (past ++ [Threaded out]) sigs r) :
    RVSDG.NestedTheta.Term.ofBase
      (.bind (RVSDG.OrderedRuntime.Structured.primitiveNode live i o op wires) (fun j => j.elim0) rest) =
    .bind (.ofBase (RVSDG.OrderedRuntime.Structured.primitiveNode live i o op wires))
      (fun j => j.elim0) (.ofBase rest) := by
  simp only [RVSDG.NestedTheta.Term.ofBase]
  congr
  funext j
  exact j.elim0

private def tailChecked (graph : Graph args) (past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)))
    (live : Origin (carrier (activationArgs args)) past runtime)
    (word : Origin (carrier (activationArgs args)) past (.value .word)) :
    Checked TailTest Effect (inputData (activationArgs args)) (.control (inputData (activationArgs args)))
      live (.ofBase (Petri.routeReturns graph
        (testAfter graph.activation.stop (.ret (withRuntime live (.cons word .nil)))))) := by
  let sorts := activationArgs args
  let tailWires : Wires (carrier sorts) (past ++ [Threaded (tagged sorts)]) (Petri.Packet args) :=
    Petri.route graph (newestWires past)
  have tailLive : (splitRuntime (tagged sorts) tailWires).2 =
      (nextRuntime past (tagged sorts) : Origin (carrier sorts) _ runtime) := by
    unfold tailWires
    rw [splitRuntime_get, route_get_heap]
    change ((identityPorts (Threaded (tagged sorts))).map (fun _ p =>
      Origin.output (newestIndex (Threaded (tagged sorts)) past) (newestPort p past))).get _ = _
    rw [get_map, identity_get]
    rfl
  have tailEq : withRuntime (nextRuntime past (tagged sorts)) (splitRuntime (tagged sorts) tailWires).1 =
      tailWires := by
    rw [← tailLive, append_split]
  have tail := Checked.ret (P := TailTest) (E := Effect)
    (a := inputData sorts) (b := Data.control (inputData sorts))
    (nextRuntime past (tagged sorts)) (splitRuntime (tagged sorts) tailWires).1
  let op := Instruction.pure (P := TailTest) (E := Effect) (.check graph.activation.stop)
  let data := Tuple.cons word (dataWires sorts (fun p => .arg p))
  have boundary :
      Petri.routeReturns graph (testAfter graph.activation.stop (.ret (withRuntime live (.cons word .nil)))) =
        .bind (RVSDG.OrderedRuntime.Structured.primitiveNode live (.value (inputData sorts))
          (.control (inputData sorts)) op data) (fun j => j.elim0) (.ret tailWires) := by
    change RVSDG.Term.bind
      (⟨Threaded (tested sorts),
        .simple (RVSDG.OrderedRuntime.Structured.Opcode.ordered
          (.value (inputData sorts)) (.control (inputData sorts)) op),
        .cons word (inputsWithHeap live sorts (fun p => .arg p)), fun j => j.elim0⟩ :
        RVSDG.Node ThetaOpcode (carrier sorts) past (Threaded (tagged sorts)))
      (fun j => j.elim0) (.ret tailWires) = _
    rw [arguments_withRuntime live sorts (fun p => .arg p)]
    rfl
  rw [boundary, ofBase_primitive, ← tailEq]
  exact Checked.primitive live _ _ op data tail

private def bodyCheckedFrom (graph : Graph args) :
    {past : List (List ValueSort)} → {version : Nat} → {target : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))} →
      (body : Body (activationArgs args) past version) →
      (routing : Memory.Routing (activationArgs args) past target) →
      (live : Origin (carrier (activationArgs args)) target runtime) →
      Checked TailTest Effect (inputData (activationArgs args)) (.control (inputData (activationArgs args))) live
        (.ofBase (Petri.routeReturns graph (testAfter graph.activation.stop
          (RVSDG.Institution.mapTerm liftMemory (body.lowerFrom routing live).term))))
  | _, _, _, .ret _ src, route, live => tailChecked graph _ live (route src)
  | _, _, _, .load _ address more, route, live => by
    change Checked TailTest Effect _ _ live (.ofBase (.bind
      (RVSDG.OrderedRuntime.Structured.primitiveNode live (.value .nil) wordData
        (.effect Effect.load) (.cons (route address) .nil)) (fun j => j.elim0) _))
    rw [ofBase_primitive]
    exact .primitive live (.value .nil) wordData (.effect Effect.load) (.cons (route address) .nil)
      (bodyCheckedFrom graph more route.afterLoad _)
  | _, _, _, .store _ address src more, route, live => by
    change Checked TailTest Effect _ _ live (.ofBase (.bind
      (RVSDG.OrderedRuntime.Structured.primitiveNode live (.value (.value .nil)) .nil
        (.effect Effect.store) (.cons (route address) (.cons (route src) .nil))) (fun j => j.elim0) _))
    rw [ofBase_primitive]
    exact .primitive live (.value (.value .nil)) .nil (.effect Effect.store) (.cons (route address) (.cons (route src) .nil))
      (bodyCheckedFrom graph more route.afterStore _)

def wrapChecked (graph : Graph args) (ports : PortMap args entry)
    (wires : Wires (carrier entry) [carrier (activationArgs args)] (dataPorts outs)) :
    EntryChecked (a := inputData entry) (b := inputData outs) (wrapTerm graph ports wires) :=
  .theta (.arg (runtimePort (dataPorts entry))) (inputData (activationArgs args))
    (seedWires graph ports) graph.activation.thetaSigs
    (fun _ => bodyCheckedFrom graph graph.activation.body (Memory.Routing.entry (activationArgs args)) _)
    (.ret _ wires)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Admission
