module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Fuel.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
import Silmaril.SSA.PEG.Bridge.ForwardCFG.Thms
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL.Proofs

open RVSDG (Port Tuple)
open ForwardCFG (Value)
open Silmaril.SSA.LambdaRTL (Val Op CFG upd obs)
open Silmaril.SSA.LambdaRTL.CFG
open RVSDG.LambdaSSA.Theta
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open Simple.Revert.While.Region (Reads Schedule)
open Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL.Compiler (Layout initial push operands packet unpack emit)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars ins outs : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1}
variable (m : TotalModel P) [DecidableEq Data]

private def Agrees (layout : Layout vars) (store : Store m) (values : Tuple m.toPEG.Value vars) : Prop :=
  ∀ t (p : Port vars t), store (layout p) = .atom t (values.get p)

private def available (bound : Nat) : Register → Prop
  | .slot _ => True
  | .temp i => i < bound
  | _ => False

private theorem available_ne_temp {reg : Register} {bound : Nat}
    (live : available bound reg) : reg ≠ .temp bound := by
  rintro rfl
  exact (Nat.lt_irrefl bound) live

private theorem available_ne_ignored {reg : Register} {bound : Nat}
    (live : available bound reg) : reg ≠ .ignored := by
  rintro rfl
  exact live

private theorem available_succ {reg : Register} {bound : Nat}
    (live : available bound reg) : available (bound + 1) reg := by
  cases reg <;> simp_all [available]
  omega

private def unpackStore : {vars : List (Ty Data)} →
    Tuple m.toPEG.Value vars → Nat → Store m → Store m
  | _, .nil, _, store => store
  | _, .cons x xs, i, store =>
    unpackStore xs (i + 1) (upd (upd store (.slot i) (.atom _ x)) (.suffix i) (Value.pack xs))

private theorem unpack_exec {R : Type} (jump : Label → Value m.toPEG.Value → Store m → Option R)
    (body : Body Register Label (Instruction P)) (values : Tuple m.toPEG.Value vars)
    (i : Nat) (src : Register) (store : Store m) (same : store src = Value.pack values) :
    (unpack body vars i src).exec (model m) jump store =
      body.exec (model m) jump (unpackStore m values i store) := by
  induction values generalizing i src store with
  | nil => rfl
  | @cons t ts x xs ih =>
    let next := upd (upd store (.slot i) (.atom t x)) (.suffix i) (Value.pack xs)
    have suffix : next (.suffix i) = Value.pack xs := by simp [next, upd]
    have read : (model m).unpair (store src) = some (.atom t x, Value.pack xs) := by
      rw [same]
      rfl
    rw [unpack, Body.exec, Op.eval, Val.eval]
    change ((model m).unpair (store src)).bind _ = _
    rw [read, Option.bind_some]
    exact ih _ _ next suffix

omit [DecidableEq Data] in
private theorem earlier_slots (values : Tuple m.toPEG.Value vars)
    (i used : Nat) (store : Store m) (earlier : used < i) :
    unpackStore m values i store (.slot used) = store (.slot used) := by
  induction values generalizing i store with
  | nil => rfl
  | cons x xs ih =>
    rw [unpackStore, ih (i + 1) _ (by omega)]
    simp [upd, show used ≠ i by omega]

omit [DecidableEq Data] in
private theorem unpack_agrees (values : Tuple m.toPEG.Value vars) (i : Nat) (store : Store m) :
    Agrees m (initial i) (unpackStore m values i store) values := by
  induction values generalizing i store with
  | nil => intro _ p; nomatch p
  | @cons t ts x xs ih =>
    intro out p
    let next := upd (upd store (.slot i) (.atom t x)) (.suffix i) (Value.pack xs)
    cases p with
    | head =>
      change unpackStore m xs (i + 1) next (.slot i) = .atom t x
      rw [earlier_slots m xs (i + 1) i next (by omega)]
      simp [next, upd]
    | tail p =>
      have offset : i + (ForwardCFG.Compiler.portIndex p + 1) =
          i + 1 + ForwardCFG.Compiler.portIndex p := by omega
      simpa only [initial, ForwardCFG.Compiler.portIndex, unpackStore, offset, Tuple.get] using
        ih (i + 1) next _ p

private theorem eval_operands (layout : Layout vars) (store : Store m)
    (values : Tuple m.toPEG.Value vars) (agrees : Agrees m layout store values)
    (slots : Tuple (Port vars) outs) :
    (operands layout slots).eval (model m) store = Value.pack (slots.map fun _ p => values.get p) := by
  induction slots with
  | nil => rfl
  | cons p ps ih => exact congrArg₂ Value.pair (agrees _ p) ih

omit [DecidableEq Data] in
private theorem tuple_ext {F : Ty Data → Type} {ts : List (Ty Data)} {xs ys : Tuple F ts}
    (pointwise : ∀ t (p : Port ts t), xs.get p = ys.get p) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have head : x = y := pointwise _ .head
      have tail : xs = ys := ih (fun t p => pointwise t (.tail p))
      rw [head, tail]

private theorem eval_packet (layout : Layout vars) (store : Store m)
    (values : Tuple m.toPEG.Value vars) (agrees : Agrees m layout store values) :
    (packet layout).eval (model m) store = Value.pack values := by
  rw [packet, eval_operands m layout store values agrees]
  apply congrArg Value.pack
  apply tuple_ext
  intro t p
  rw [Simple.get_map, Simple.ports_get]

omit [DecidableEq Data] in
private theorem args_eval {scope : Tuple (Ref g.sort) vars} {refs : Tuple (Ref g.sort) ins}
    (reads : Reads scope refs) (values : Tuple m.toPEG.Value vars) :
    reads.args.eval m.toPEG values = some (reads.slots.map fun _ p => values.get p) := by
  induction reads with
  | nil => rfl
  | cons _ _ _ ih => simp [Reads.args, Reads.slots, Simple.Args.eval, Simple.Expr.evalLift, Tuple.map, ih]

private theorem primitive_eval (op : P ins t) (args : Tuple m.toPEG.Value ins) :
    (model m).app (.inl ⟨ins, t, .primitive op⟩) (Value.pack args) =
      some (.atom t (m.run op args)) := by
  change ((Value.pack args).unpack ins).map (fun xs => Value.atom t (m.run op xs)) = _
  rw [Value.unpack_pack]
  rfl

private theorem emit_exec {R : Type} (result : Option R → Prop)
    {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Schedule g false roots scope) (layout : Layout vars) (next : Nat)
    (finish : Layout outs → Term Register Label (Instruction P))
    (jump : Label → Value m.toPEG.Value → Store m → Option R)
    (store : Store m) (values : Tuple m.toPEG.Value vars) (output : Tuple m.toPEG.Value outs)
    (agrees : Agrees m layout store values)
    (live : ∀ t (p : Port vars t), available next (layout p))
    (ran : schedule.lower.runLoopFree m.toPEG values = some output)
    (continued : ∀ (layout : Layout outs) (next : Nat) (store : Store m),
      Agrees m layout store output → (∀ t (p : Port outs t), available next (layout p)) →
      result ((finish layout).exec (model m) jump store)) :
    result ((emit schedule layout next finish).exec (model m) jump store) := by
  induction schedule generalizing next store with
  | done reads =>
    have projected : reads.slots.map (fun _ p => values.get p) = output := Option.some.inj ran
    refine continued _ next store (fun t p => ?_) (fun t p => live t (reads.slots.get p))
    rw [← projected, Simple.get_map]
    exact agrees t (reads.slots.get p)
  | bind i op refs fresh row reads tail ih =>
    let args := reads.slots.map fun _ p => values.get p
    let assigned := upd store (.temp next) (.atom (g.sort i) (m.run op args))
    have called : (Op.app (.inl ⟨_, _, .primitive op⟩) (operands layout reads.slots)).eval (model m) store =
        some (.atom (g.sort i) (m.run op args)) := by
      rw [Op.eval, eval_operands m layout store values agrees]
      exact primitive_eval m op args
    have rest : tail.lower.runLoopFree m.toPEG (.cons (m.run op args) values) = some output := by
      simpa only [Schedule.lower, Simple.Stmt.runLoopFree, Simple.Expr.eval, Simple.Expr.evalLift,
        args_eval m reads values, TotalModel.toPEG, Option.elim, Option.map_some, Option.bind_some] using ran
    have ready : Agrees m (push layout next) assigned (.cons (m.run op args) values) := by
      intro out p
      cases p with
      | head => simp [push, assigned, upd, Tuple.get]
      | tail p =>
        have unused := available_ne_temp (live _ p)
        simpa only [push, assigned, upd, ite_eq_right unused, Tuple.get] using agrees _ p
    have later : ∀ t (p : Port (g.sort i :: _) t), available (next + 1) ((push layout next) p) := by
      intro t p
      cases p with
      | head => exact Nat.lt_succ_self _
      | tail p => exact available_succ (live _ p)
    simpa only [emit, Body.exec, called, Option.bind_eq_bind, Option.bind_some] using
      ih (push layout next) (next + 1) finish assigned _ output ready later rest continued
  | branch enabled => cases enabled

variable {g' : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
variable (b : Bundle g' slot invariants)

private abbrev Transfer (m : TotalModel P) := Cyclic.Transfer Register Label (Value m.toPEG.Value)

private def transferTo (m : TotalModel P) (label : Label) (value : Value m.toPEG.Value) (store : Store m) :
    Option (Transfer m ⊕ Transfer m) :=
  some (.inr (label, value, store))

/-- The before block executes only the checked guard. Both branch leaves
pass the guard's old-state packet in the original slot order. -/
private theorem before_step (input old : Tuple m.toPEG.Value carried) (guard : ULift Bool) (store : Store m)
    (tested : b.scalar.guard.lower.runLoopFree m.toPEG input = some (.cons guard old)) :
    ∃ final, Cyclic.step (model m) (lower b).blocks (.before, Value.pack input, store) =
      some (.inr (if guard.down then .after else .exit, Value.pack old, final)) := by
  let incoming := upd store Register.packet (Value.pack input)
  have loaded : incoming .packet = Value.pack input := by simp [incoming, upd]
  change ∃ final, (before b).exec (model m) (transferTo m) incoming =
    some (.inr (if guard.down then .after else .exit, Value.pack old, final))
  rw [before, unpack_exec m (transferTo m) _ input 0 .packet incoming loaded]
  refine emit_exec m (fun result => ∃ final, result =
      some (.inr (if guard.down then .after else .exit, Value.pack old, final)))
    b.scalar.guard (initial 0) 0 _ (transferTo m) _ input (.cons guard old)
    (unpack_agrees m input 0 incoming) (fun _ _ => True.intro) tested ?_
  intro layout next σ agrees live
  let final := upd σ Register.ignored Value.unit
  have kept : Agrees m (fun p => layout (.tail p)) final old := by
    intro t p
    have h := available_ne_ignored (live t (.tail p))
    change upd σ Register.ignored Value.unit (layout (.tail p)) = _
    rw [upd, ite_eq_right h]
    exact agrees t (.tail p)
  have latched := eval_packet m (fun p => layout (.tail p)) final old kept
  have test : (Op.app (.inr ()) (.var (layout .head))).eval (model m) σ =
      some (if guard.down then .inr .unit else .inl .unit) := by
    rw [Op.eval, Val.eval, agrees _ .head]
    rfl
  refine ⟨final, ?_⟩
  obtain ⟨flag⟩ := guard
  rw [Term.exec, test]
  cases flag
  · change transferTo m .exit ((packet fun p => layout (.tail p)).eval (model m) final) final = _
    rw [latched]
    rfl
  · change transferTo m .after ((packet fun p => layout (.tail p)).eval (model m) final) final = _
    rw [latched]
    rfl

private theorem after_step (old next : Tuple m.toPEG.Value carried) (store : Store m)
    (updated : b.scalar.update.lower.runLoopFree m.toPEG old = some next) :
    ∃ final, Cyclic.step (model m) (lower b).blocks (.after, Value.pack old, store) =
      some (.inr (.before, Value.pack next, final)) := by
  let incoming := upd store Register.packet (Value.pack old)
  have loaded : incoming .packet = Value.pack old := by simp [incoming, upd]
  change ∃ final, (after b).exec (model m) (transferTo m) incoming =
    some (.inr (.before, Value.pack next, final))
  rw [after, unpack_exec m (transferTo m) _ old 0 .packet incoming loaded]
  refine emit_exec m (fun result => ∃ final, result = some (.inr (.before, Value.pack next, final)))
    b.scalar.update (initial 0) 0 _ (transferTo m) _ old next
    (unpack_agrees m old 0 incoming) (fun _ _ => True.intro) updated ?_
  intro layout _ σ agrees _
  refine ⟨σ, ?_⟩
  change transferTo m .before ((packet layout).eval (model m) σ) σ = _
  rw [eval_packet m layout σ next agrees]
  rfl

private theorem runFrom_eq (fuel slack : Nat) (small : slack ≤ 1)
    (input : Tuple m.toPEG.Value carried) (store : Store m) :
    (Cyclic.runFromFuel (model m) (lower b).blocks (2 * fuel + slack)
      (.before, Value.pack input, store)).map obs =
      (Operational.runFuel (Region.model m) b.compile fuel (encode m input)).map
        (fun result => (Label.exit, Value.pack (fromPorts (F := (Region.model m).Val) carried result))) := by
  induction fuel generalizing input store with
  | zero =>
    have budget : slack = 0 ∨ slack = 1 := by omega
    rcases budget with rfl | rfl
    · rfl
    · obtain ⟨guard, old, _, tested, _, _⟩ := Region.body_run b.scalar m input
      obtain ⟨final, testedStep⟩ := before_step m b input old guard store tested
      change (Cyclic.runFromFuel (model m) (lower b).blocks 1
        (.before, Value.pack input, store)).map obs = none
      rw [Cyclic.runFromFuel, testedStep]
      rfl
  | succ fuel ih =>
    obtain ⟨guard, old, next, tested, updated, numbered⟩ := Region.body_run b.scalar m input
    obtain ⟨testedStore, testedStep⟩ := before_step m b input old guard store tested
    rw [show 2 * (fuel + 1) + slack = 2 * fuel + slack + 2 by omega,
      Cyclic.runFromFuel, testedStep, Operational.runFuel, numbered, Operational.split_bodyResult]
    obtain ⟨flag⟩ := guard
    cases flag
    · have exited : Cyclic.step (model m) (lower b).blocks (.exit, Value.pack old, testedStore) =
          some (.inl (.exit, Value.pack old, testedStore)) := rfl
      change (Cyclic.runFromFuel (model m) (lower b).blocks (2 * fuel + slack + 1)
        (.exit, Value.pack old, testedStore)).map obs =
        some (Label.exit, Value.pack (fromPorts (F := (Region.model m).Val) carried (encode m old)))
      rw [Cyclic.runFromFuel, exited]
      exact congrArg (fun vals => some (Label.exit, Value.pack vals)) (from_toPorts (F := (Region.model m).Val) old).symm
    · obtain ⟨updatedStore, updateStep⟩ := after_step m b old next testedStore updated
      change (Cyclic.runFromFuel (model m) (lower b).blocks (2 * fuel + slack + 1)
        (.after, Value.pack old, testedStore)).map obs = _
      rw [Cyclic.runFromFuel, updateStep]
      exact ih next updatedStore

theorem observeFuel_eq (fuel : Nat) (input : Tuple m.toPEG.Value carried) :
    observeFuel b m fuel input =
      (Operational.runFuel (Region.model m) b.compile (fuel / 2) (encode m input)).map
        (fun result => (Label.exit, Value.pack (fromPorts (F := (Region.model m).Val) carried result))) := by
  have paired : 2 * (fuel / 2) + fuel % 2 = fuel := by omega
  have ran := runFrom_eq m b (fuel / 2) (fuel % 2) (by omega) input (inputStore m input)
  rw [paired] at ran
  exact ran

private theorem packed_result {a : Tuple (Region.model m).Val (valuePorts carried)}
    {output : Tuple m.toPEG.Value carried}
    (same : Value.pack (fromPorts (F := (Region.model m).Val) carried a) = Value.pack output) :
    a = encode m output := by
  have unpacked := congrArg (Value.unpack carried) same
  rw [Value.unpack_pack, Value.unpack_pack] at unpacked
  have transported := congrArg (encode m) (Option.some.inj unpacked)
  exact (to_fromPorts a).symm.trans transported

theorem returns_iff_numbered (input output : Tuple m.toPEG.Value carried) :
    (∃ fuel, observeFuel b m fuel input = some (.exit, Value.pack output)) ↔
      b.compile.Returns (Region.model m) (encode m input) (encode m output) := by
  rw [Operational.returns_iff_runFuel]
  constructor
  · rintro ⟨fuel, ran⟩
    rw [observeFuel_eq] at ran
    obtain ⟨result, evaluation, same⟩ := Option.map_eq_some_iff.mp ran
    exact ⟨fuel / 2, evaluation.trans (congrArg some (packed_result m (Prod.mk.inj same).2))⟩
  · rintro ⟨fuel, ran⟩
    refine ⟨2 * fuel, ?_⟩
    rw [observeFuel_eq, show 2 * fuel / 2 = fuel by omega, ran]
    exact congrArg (fun vals => some (Label.exit, Value.pack vals)) (from_toPorts (F := (Region.model m).Val) output)

theorem mem_observe_iff (input : Tuple m.toPEG.Value carried) (label : Label) (value : Value m.toPEG.Value) :
    (label, value) ∈ observe b m input ↔ ∃ fuel, observeFuel b m fuel input = some (label, value) := by
  unfold observe
  change _ ∈ Part.map obs _ ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨result, member, same⟩
    obtain ⟨fuel, ran⟩ := (Cyclic.mem_run_iff_runFuel (model m) (lower b) (inputStore m input) result).mp member
    exact ⟨fuel, Option.map_eq_some_iff.mpr ⟨result, ran, same⟩⟩
  · rintro ⟨fuel, ran⟩
    obtain ⟨result, evaluation, same⟩ := Option.map_eq_some_iff.mp ran
    exact ⟨result, (Cyclic.mem_run_iff_runFuel (model m) (lower b) (inputStore m input) result).mpr
      ⟨fuel, evaluation⟩, same⟩

theorem observe_result (input : Tuple m.toPEG.Value carried) {label : Label}
    {value : Value m.toPEG.Value} (ran : (label, value) ∈ observe b m input) :
    ∃ output : Tuple m.toPEG.Value carried, label = .exit ∧ value = Value.pack output := by
  obtain ⟨fuel, evaluated⟩ := (mem_observe_iff m b input label value).mp ran
  rw [observeFuel_eq] at evaluated
  obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp evaluated
  obtain ⟨labelEq, valueEq⟩ := Prod.mk.inj same.symm
  exact ⟨fromPorts (F := (Region.model m).Val) carried result, labelEq, valueEq⟩

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL.Proofs
