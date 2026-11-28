module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Defs
public import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
public import Silmaril.SSA.PEG.Simple.Thms
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Proofs

open RVSDG (Origin Locals Port Tuple Wires)
open Simple.Revert.While.Region (Certificate Schedule Reads)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Compiler

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars outs ins : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}
variable {past : List (List (ValuePort Data))}
variable (m : TotalModel P)

private def read {t : ValuePort Data}
    (wire : Origin (valuePorts carried) past t) (entry : Tuple m.toPEG.Value carried)
    (locals : Locals (model m).Val past) : (model m).Val t :=
  (Wires.read (.cons wire .nil) (encode m entry) locals).get .head

private theorem readLast {head : List (ValuePort Data)} {t : ValuePort Data}
    (entry : Tuple m.toPEG.Value carried) (locals : Locals (model m).Val past)
    (out : Tuple (model m).Val head) (slot : Port head t) :
    read m (last past slot) entry (locals.snoc out) = out.get slot := by
  induction past with
  | nil => rfl
  | cons a rest ih => exact ih locals.2

private theorem readWeaken {head : List (ValuePort Data)} {t : ValuePort Data}
    (entry : Tuple m.toPEG.Value carried) (locals : Locals (model m).Val past)
    (out : Tuple (model m).Val head) (wire : Origin (valuePorts carried) past t) :
    read m (Bridge.Compiler.weaken head wire) entry (locals.snoc out) =
      read m wire entry locals := by
  cases wire with
  | arg => rfl
  | output i p =>
    induction past with
    | nil => exact i.elim0
    | cons a rest ih =>
      refine Fin.cases (motive := fun j => ∀ q : Port (a :: rest)[j] t,
        read m (Bridge.Compiler.weaken head (.output (past := a :: rest) j q)) entry (locals.snoc out) =
          read m (.output (past := a :: rest) j q) entry locals) ?_ ?_ i p
      · intro q
        rfl
      · intro j q
        exact ih locals.2 j q

private theorem encode_get (xs : Tuple m.toPEG.Value vars) (p : Port vars t) :
    (encode m xs).get (portToValue p) = xs.get p := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ xs => exact ih xs

private theorem ports_select {F : Ty Data → Type} (xs : Tuple F vars) :
    (Simple.ports vars).map (fun _ p => xs.get p) = xs := by
  induction xs with
  | nil => rfl
  | @cons t ts x xs ih =>
    change Tuple.cons x (((Simple.ports ts).map fun _ p => Port.tail p).map
      (fun _ p => (Tuple.cons x xs).get p)) = _
    have tail : ∀ {outs : List (Ty Data)} (slots : Tuple (Port ts) outs),
        ((slots.map fun _ p => Port.tail p).map
          (fun _ p => (Tuple.cons x xs).get p)) = slots.map (fun _ p => xs.get p) := by
      intro outs slots
      induction slots with
      | nil => rfl
      | cons _ _ ih => exact congrArg (Tuple.cons _) ih
    rw [tail, ih]

/-- Projecting the old carried tuple removes only the cached guard. -/
theorem project_old {F : Ty Data → Type} (flag : F .bool) (xs : Tuple F vars) :
    ((Simple.ports vars).map (fun _ p => Port.tail (s := Ty.bool) p)).map
      (fun _ p => (Tuple.cons flag xs).get p) = xs :=
  congrArg (fun ys : Tuple F (.bool :: vars) => match ys with | .cons _ tail => tail)
    (ports_select (Tuple.cons flag xs))

private abbrev Agrees (scope : Scope carried vars past) (entry : Tuple m.toPEG.Value carried)
    (locals : Locals (model m).Val past) (store : Tuple m.toPEG.Value vars) : Prop :=
  ∀ {t} (p : Port vars t), read m (scope p) entry locals = store.get p

private theorem initial (entry : Tuple m.toPEG.Value carried)
    (locals : Locals (model m).Val past) :
    Agrees m Scope.initial entry locals entry :=
  fun p => encode_get m entry p

private theorem push_agrees (scope : Scope carried vars past)
    (entry : Tuple m.toPEG.Value carried) (locals : Locals (model m).Val past)
    (store : Tuple m.toPEG.Value vars) (agree : Agrees m scope entry locals store)
    (value : m.toPEG.Value t) :
    Agrees m (scope.push (t := t)) entry (locals.snoc (.cons value .nil)) (.cons value store) := by
  intro u p
  cases p with
  | head => exact readLast m entry locals (encode m (.cons value .nil)) .head
  | tail p => exact (readWeaken m entry locals (encode m (.cons value .nil)) (scope p)).trans (agree p)

private theorem wires_read (scope : Scope carried vars past)
    (entry : Tuple m.toPEG.Value carried) (locals : Locals (model m).Val past)
    (store : Tuple m.toPEG.Value vars) (agree : Agrees m scope entry locals store)
    (slots : Tuple (Port vars) outs) :
    (wires scope slots).read (encode m entry) locals = encode m (slots.map (fun _ p => store.get p)) := by
  induction slots with
  | nil => rfl
  | cons p _ ih => exact congrArg₂ Tuple.cons (agree p) ih

private theorem args_read (entry : Tuple m.toPEG.Value carried)
    (locals : Locals (model m).Val past) :
    (args carried past).read (encode m entry) locals = encode m entry := by
  rw [args, wires_read m Scope.initial entry locals entry (initial m entry locals), ports_select]

private theorem eval_reads {sort : Fin n → Ty Data} {scope : Tuple (Ref sort) vars}
    {refs : Tuple (Ref sort) ins} (reads : Reads scope refs) (store : Tuple m.toPEG.Value vars) :
    reads.args.eval m.toPEG store = some (reads.slots.map (fun _ p => store.get p)) := by
  induction reads with
  | nil => rfl
  | cons p _ tail ih =>
    rw [Reads.args, Simple.Args.eval, Simple.Expr.evalLift, ih]
    rfl

private theorem slice_eval {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    {results : List (ValuePort Data)} (schedule : Schedule g false roots scope)
    (layout : Scope carried vars past) (entry : Tuple m.toPEG.Value carried)
    (locals : Locals (model m).Val past) (store : Tuple m.toPEG.Value vars)
    (agree : Agrees m layout entry locals store)
    (finish : ∀ {past'}, Wires (valuePorts carried) past' (valuePorts outs) → Code P carried past' results)
    (denote : Tuple m.toPEG.Value outs → Tuple (model m).Val results)
    (finish_ok : ∀ (past') (w : Wires (valuePorts carried) past' (valuePorts outs))
      (ls : Locals (model m).Val past') (vs : Tuple m.toPEG.Value outs),
      w.read (encode m entry) ls = encode m vs →
        (finish w).2.eval (model m) (encode m entry) ls = denote vs) :
    ∃ values, schedule.lower.runLoopFree m.toPEG store = some values ∧
      (slice schedule layout finish).2.eval (model m) (encode m entry) locals = denote values := by
  induction schedule generalizing past with
  | done reads =>
    let values := reads.slots.map (fun _ p => store.get p)
    exact ⟨values, rfl, finish_ok _ _ locals values (wires_read m layout entry locals store agree reads.slots)⟩
  | bind i op refs fresh row reads tail ih =>
    let operands := reads.slots.map (fun _ p => store.get p)
    let value := m.run op operands
    have read_ok := wires_read m layout entry locals store agree reads.slots
    have prim : (model m).run (Opcode.primitive op)
        ((wires layout reads.slots).read (encode m entry) locals) =
        encode m (.cons value .nil) := by
      rw [read_ok]
      change Tuple.cons (F := (model m).Val) (t := .value (g.sort i))
        (m.run op (fromPorts _ (encode m operands))) .nil = _
      rw [from_toPorts]
      rfl
    have agrees : Agrees m layout.push entry (locals.snoc (.cons value .nil)) (.cons value store) :=
      push_agrees m (t := g.sort i) layout entry locals store agree value
    obtain ⟨values, ran, denoted⟩ :=
      ih layout.push (locals.snoc (.cons value .nil)) (.cons value store) (fun p => agrees p)
        finish denote finish_ok
    refine ⟨values, ?_, ?_⟩
    · change (((Simple.Args.eval m.toPEG store reads.args).elim none (m.toPEG.run op)).map
        (fun x => Tuple.cons (F := m.toPEG.Value) x store)).bind (tail.lower.runLoopFree m.toPEG) = _
      rw [eval_reads]
      exact ran
    · change (slice tail layout.push finish).2.eval (model m) (encode m entry)
        (locals.snoc ((model m).run (Opcode.primitive op)
          ((wires layout reads.slots).read (encode m entry) locals))) = _
      rw [prim]
      exact denoted
  | branch enabled => nomatch enabled

/-- Both schedules succeed on every defined old store under the total primitive model. -/
theorem schedules_total (cert : Certificate g allowInvariant) : cert.Total m.toPEG := by
  constructor
  · intro store
    obtain ⟨values, ran, _⟩ := slice_eval m cert.guard Scope.initial store (past := []) PUnit.unit store
      (initial (past := []) m store PUnit.unit) (fun w => ⟨[], .ret w⟩) (encode m) (fun _ _ _ _ h => h)
    exact ⟨values, ran⟩
  · intro store
    obtain ⟨values, ran, _⟩ := slice_eval m cert.update Scope.initial store (past := []) PUnit.unit store
      (initial (past := []) m store PUnit.unit) (fun w => ⟨[], .ret w⟩) (encode m) (fun _ _ _ _ h => h)
    exact ⟨values, ran⟩

private theorem continue_eval (cert : Certificate g allowInvariant) (entry : Tuple m.toPEG.Value carried) :
    ∃ values, cert.update.lower.runLoopFree m.toPEG entry = some values ∧
      (continueArm cert).2.run (model m) (encode m entry) = encode m values :=
  slice_eval m cert.update Scope.initial entry (past := []) PUnit.unit entry
    (initial (past := []) m entry PUnit.unit) (fun w => ⟨[], .ret w⟩) (encode m) (fun _ _ _ _ h => h)

private theorem payload_read (entry : Tuple m.toPEG.Value carried) (locals : Locals (model m).Val past)
    (xs : Tuple (model m).Val (valuePorts carried)) :
    (wires (fun p => last past (portToValue p)) (Simple.ports carried)).read
      (encode m entry) (locals.snoc xs) = xs := by
  let decoded := fromPorts (F := (model m).Val) carried xs
  have same : encode m decoded = xs := to_fromPorts xs
  have agree : Agrees m (fun p => last past (portToValue p)) entry (locals.snoc xs) decoded := by
    intro t p
    exact (readLast m entry locals xs (portToValue p)).trans
      ((congrArg (fun ys => Tuple.get ys (portToValue p)) same.symm).trans (encode_get m decoded p))
  rw [wires_read m _ entry _ decoded agree, ports_select, same]

private theorem wires_weaken {head : List (ValuePort Data)} {ts : List (ValuePort Data)}
    (xs : Wires (valuePorts carried) past ts) (entry : Tuple m.toPEG.Value carried)
    (locals : Locals (model m).Val past) (out : Tuple (model m).Val head) :
    (Wires.read (xs.map fun _ w => Bridge.Compiler.weaken head w) (encode m entry) (locals.snoc out)) =
      xs.read (encode m entry) locals := by
  induction xs with
  | nil => rfl
  | cons w _ ih => exact congrArg₂ Tuple.cons (readWeaken m entry locals out w) ih

private theorem select_eval (cert : Certificate g allowInvariant)
    (entry old next : Tuple m.toPEG.Value carried)
    (updated : (continueArm cert).2.run (model m) (encode m old) = encode m next)
    (locals : Locals (model m).Val past) (flag : Origin (valuePorts carried) past (.value .bool))
    (wire : Wires (valuePorts carried) past (valuePorts carried))
    (again : Bool) (tested : read m flag entry locals = ⟨again⟩)
    (captured : wire.read (encode m entry) locals = encode m old) :
    (select cert flag wire).2.eval (model m) (encode m entry) locals =
      RVSDG.Theta.bodyResult (model m) again (encode m (if again then next else old)) := by
  let tag : Tuple (model m).Val [.control 2] := .cons ⟨if again then 1 else 0⟩ .nil
  let afterTag := locals.snoc tag
  let tagWire := last (entry := valuePorts carried) (head := [.control 2]) past .head
  have tag_read : read m tagWire entry afterTag = tag.get .head :=
    readLast m entry locals tag .head
  let execute := fun (i : Fin 2) input => (selectArm cert wire i).run (model m) input
  let result := RVSDG.Shape.eval (model m) (selectNode cert wire).shape execute
    ((selectNode cert wire).inputs.read (encode m entry) afterTag)
  have branch_input : (branchNode (P := P) flag).inputs.read (encode m entry) locals =
      Tuple.cons (F := (model m).Val) (t := .value .bool) ⟨again⟩ .nil := by
    change Tuple.cons (F := (model m).Val) (t := .value .bool) (read m flag entry locals) .nil = _
    rw [tested]
  simp only [select, RVSDG.Term.eval, branch_input]
  change Tuple.cons (F := (model m).Val)
      (read m (Bridge.Compiler.weaken (valuePorts carried) tagWire) entry (afterTag.snoc result))
      ((wires (fun p => last (past ++ [[.control 2]]) (portToValue p)) (Simple.ports carried)).read
        (encode m entry) (afterTag.snoc result)) = _
  rw [readWeaken, tag_read, payload_read]
  have input_eq : (selectNode cert wire).inputs.read (encode m entry) afterTag =
      .cons (tag.get .head) (encode m old) := by
    change Tuple.cons (read m tagWire entry afterTag)
      (Wires.read (wire.map (fun _ w => Bridge.Compiler.weaken [.control 2] w))
        (encode m entry) afterTag) = _
    rw [tag_read, wires_weaken, captured]
  unfold result
  rw [input_eq]
  change Tuple.cons (F := (model m).Val) (tag.get .head)
      (execute (tag.get .head).down (encode m old)) = _
  cases again
  · exact congrArg (Tuple.cons (tag.get .head)) (args_read (past := []) m old PUnit.unit)
  · exact congrArg (Tuple.cons (tag.get .head)) updated

/-- The numbered θ body tests the projected old vector and selects identity
or the checked update slice. -/
theorem body_run (cert : Certificate g allowInvariant) (entry : Tuple m.toPEG.Value carried) :
    ∃ (guard : ULift Bool) (old next : Tuple m.toPEG.Value carried),
      cert.guard.lower.runLoopFree m.toPEG entry = some (.cons guard old) ∧
      cert.update.lower.runLoopFree m.toPEG old = some next ∧
      (compile cert).body.run (model m) (encode m entry) =
        RVSDG.Theta.bodyResult (model m) guard.down (encode m (if guard.down then next else old)) := by
  let nextTuple := fun old =>
    fromPorts (F := (model m).Val) carried ((continueArm cert).2.run (model m) (encode m old))
  let result := fun tagged : Tuple m.toPEG.Value (.bool :: carried) =>
    match tagged with
    | .cons b old =>
      RVSDG.Theta.bodyResult (model m) b.down (encode m (if b.down then nextTuple old else old))
  have finished : ∀ past (w : Wires (valuePorts carried) past (valuePorts (.bool :: carried)))
      (ls : Locals (model m).Val past) (vs : Tuple m.toPEG.Value (.bool :: carried)),
      w.read (encode m entry) ls = encode m vs →
      (guardFinish cert w).2.eval (model m) (encode m entry) ls =
        result vs := by
    intro past w ls vs read_ok
    cases w with
    | cons flag rest =>
      cases vs with
      | cons b old =>
        have head := congrArg (fun ys : Tuple (model m).Val (valuePorts (.bool :: carried)) =>
          ys.get .head) read_ok
        have tail := congrArg (fun ys : Tuple (model m).Val (valuePorts (.bool :: carried)) =>
          match ys with | .cons _ rest => rest) read_ok
        exact select_eval m cert entry old (nextTuple old) (to_fromPorts _).symm ls flag rest b.down head tail
  obtain ⟨tagged, tested, denoted⟩ := slice_eval m cert.guard Scope.initial entry (past := []) PUnit.unit
    entry (initial (past := []) m entry PUnit.unit) (guardFinish cert) result finished
  cases tagged with
  | cons guard old =>
    obtain ⟨next, updated, ran⟩ := continue_eval m cert old
    have exactNext : nextTuple old = next :=
      (congrArg (fromPorts (F := (model m).Val) carried) ran).trans (from_toPorts (F := (model m).Val) next)
    refine ⟨guard, old, next, tested, updated, ?_⟩
    change (Compiler.body cert).2.toGraph.run (model m) (encode m entry) = _
    rw [RVSDG.Term.run_toGraph]
    simpa only [Compiler.body, RVSDG.Term.run, result, exactNext] using denoted

end Silmaril.SSA.PEG.Bridge.Theta.Region.Proofs
