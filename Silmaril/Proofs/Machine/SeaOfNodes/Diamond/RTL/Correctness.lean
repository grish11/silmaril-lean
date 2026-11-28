module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Diamond.RTL.Proofs

open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Graph Projection Val ValueSort dataPorts read sortValue)
open Silmaril.SSA.RVSDG (Locals Origin Port PortType Tuple Wires extend)
open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (CallOracle Frame)
open Silmaril.Machine.RTL.SSA (Block Func Op Prog State StepsNWithin Transition)

variable {sigs past : List (List PortTy)}

private def ArgsMatch {ports : List PortTy}
    (argReg : ∀ {t}, Port ports t → Reg) (fr : Frame Reg) (input : Tuple (Val model.value) ports) : Prop :=
  ∀ {t} (p : Port ports t), fr.get (argReg p) = some (encodeValue t (input.get p))

private def LocalsMatch (fr : Frame Reg) (base : Nat) :
    {past : List (List PortTy)} → Locals (Val model.value) past → Prop
  | [], _ => True
  | _ :: _, xs =>
    (∀ {t : PortTy} (p : Port _ t), fr.get (.node base) = some (encodeValue t (xs.1.get p))) ∧
      LocalsMatch fr (base + 1) xs.2

private def initialFrame (x y : Word) : Frame Reg :=
  (Frame.empty.set (.arg 0) x).set (.arg 1) y

private theorem initial_args (x y : Word) : ArgsMatch (fun p => .arg (portIndex p)) (initialFrame x y) (entry x y) := by
  intro t p
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p => nomatch p

private theorem locals_read {fr : Frame Reg} {base : Nat} {t : PortTy}
    (xs : Locals (Val model.value) past) (matched : LocalsMatch fr base xs)
    (i : Fin past.length) (p : Port past[i] t) :
    fr.get (.node (base + i.val)) = some (encodeValue t ((xs.get i).get p)) := by
  induction past generalizing base with
  | nil => exact i.elim0
  | cons head tail ih =>
    cases i using Fin.cases with
    | zero => exact matched.1 p
    | succ i =>
      change fr.get (.node (base + i.succ.val)) = some (encodeValue t ((xs.2.get i).get p))
      simpa only [Fin.val_succ, Nat.add_succ, Nat.succ_add] using
        ih xs.2 matched.2 i p

private theorem read_origin {ports : List PortTy} {argReg : ∀ {t}, Port ports t → Reg}
    {input : Tuple (Val model.value) ports} {fr : Frame Reg} {t : PortTy}
    {xs : Locals (Val model.value) past} (ha : ArgsMatch (fun p => argReg p) fr input)
    (hl : LocalsMatch fr 0 xs) (w : Origin ports past t) :
    fr.get (registerWith (fun p => argReg p) w) = some (encodeValue t (read model w input xs)) := by
  cases w with
  | arg p => exact ha p
  | output i p =>
    change fr.get (.node i.val) = some (encodeValue t ((xs.get i).get p))
    simpa only [Nat.zero_add] using locals_read xs hl i p

private theorem append_local {fr : Frame Reg} {base : Nat} {out : ValueSort Unit}
    (xs : Locals (Val model.value) past) (v : sortValue model.value out)
    (matched : LocalsMatch fr base xs) :
    LocalsMatch (fr.set (.node (base + past.length)) (encodeValue (.value out) v)) base
      (xs.snoc (Tuple.cons (F := Val model.value) (t := PortType.value out) v .nil)) := by
  induction past generalizing base with
  | nil =>
    constructor
    · intro t p
      cases p with
      | head =>
        simp
        rfl
      | tail p => nomatch p
    · exact trivial
  | cons head tail ih =>
    constructor
    · intro t p
      have fresh : base ≠ base + (head :: tail).length := by simp
      change (fr.set (.node (base + (head :: tail).length)) _).get (.node base) =
        some (encodeValue t (xs.1.get p))
      simpa [Frame.get_set, fresh] using matched.1 p
    · have index : base + (head :: tail).length = base + 1 + tail.length := by
        simp only [List.length_cons]
        omega
      rw [index]
      exact ih xs.2 matched.2

private theorem emit_exec {ports : List PortTy} {sorts : List (ValueSort Unit)} {out : ValueSort Unit}
    (argReg : ∀ {t}, Port ports t → Reg) (input : Tuple (Val model.value) ports)
    (op : WordOp sorts out) (wires : Wires ports past (dataPorts sorts))
    (fr : Frame Reg) (mem : Memory) (xs : Locals (Val model.value) past)
    (readWire : ∀ {t : PortTy} (wire : Origin ports past t),
      fr.get (registerWith (fun p => argReg p) wire) = some (encodeValue t (read model wire input xs))) :
    (emitOpWith (fun p => argReg p) (.node past.length) op wires).exec fr mem =
      some (fr.set (.node past.length) (encodeValue (.value out) (model.run op (wires.read input xs))), mem) := by
  have readWireWith {t : PortTy} (wire : Origin ports past t) :
      fr.get (registerWithResults (fun p => argReg p) Reg.node wire) =
        some (encodeValue t (read model wire input xs)) := readWire wire
  cases op with
  | const v => cases wires; rfl
  | add | sub | eq | ne | slt =>
    cases wires with
    | cons left rest =>
      cases rest with
      | cons right tail =>
        cases tail
        simp only [emitOpWith, emitOpWithResults, Op.exec, Tuple.get, readWireWith, Option.bind_some]
        rfl

private theorem simulate_ops {ports : List PortTy} (argReg : ∀ {t}, Port ports t → Reg)
    (separate : ∀ {t} (p : Port ports t) (i : Nat), argReg p ≠ .node i)
    (oracle : CallOracle) (input : Tuple (Val model.value) ports) (mem : Memory)
    (flow : Dataflow WordOp ports past sigs) (fr : Frame Reg) (xs : Locals (Val model.value) past)
    (ha : ArgsMatch (fun p => argReg p) fr input) (hl : LocalsMatch fr 0 xs) :
    ∃ final, Silmaril.Machine.RTL.SSA.Ops.Exec oracle (emitOpsWith (fun p => argReg p) flow) fr mem final mem ∧
      ArgsMatch (fun p => argReg p) final input ∧ LocalsMatch final 0 (flow.eval model input xs) := by
  induction flow generalizing fr with
  | nil => exact ⟨fr, .nil, ha, hl⟩
  | @cons past sigs sorts out op wires rest ih =>
    let v := model.run op (wires.read input xs)
    let next := fr.set (.node past.length) (encodeValue (.value out) v)
    have next_args : ArgsMatch (fun p => argReg p) next input := by
      intro t p
      simpa only [next, Frame.get_set, ite_eq_right (separate p past.length)] using ha p
    have next_locals : LocalsMatch next 0
        (xs.snoc (Tuple.cons (F := Val model.value) (t := PortType.value out) v .nil)) := by
      simpa only [Nat.zero_add] using append_local (base := 0) xs v hl
    obtain ⟨final, steps, argsAgree, localsAgree⟩ := ih next _ next_args next_locals
    exact ⟨final, .op (emit_exec (fun p => argReg p) input op wires fr mem xs (read_origin ha hl)) steps,
      argsAgree, localsAgree⟩


-- Every instruction in a straight-line execution with no call oracle takes
-- exactly one machine step. The existing Ops.Exec certificate supplies the effects.
private theorem counted_steps {prog : Prog Reg} {func label : Nat} {block : Block Reg}
    (found : prog.block? func label = some block)
    {ops : List (Op Reg)} {fr ready : Frame Reg} {initial final : Memory}
    (executed : Silmaril.Machine.RTL.SSA.Ops.Exec (fun _ _ _ _ _ => False) ops fr initial ready final)
    (prefixOps : List (Op Reg)) (code : block.ops = prefixOps ++ ops) :
    StepsNWithin prog [] ops.length ⟨⟨func, label, prefixOps.length⟩, fr, [], initial⟩
      ⟨⟨func, label, (prefixOps ++ ops).length⟩, ready, [], final⟩ := by
  induction executed generalizing prefixOps with
  | nil => rw [List.append_nil]; exact .refl
  | @op op rest fr mid ready initial middle final effect _ ih =>
    have atIndex : block.ops[prefixOps.length]? = some op := by rw [code]; simp
    have remaining := ih (prefixOps ++ [op]) (by rw [code]; simp)
    rw [show (prefixOps ++ [op]).length = prefixOps.length + 1 by simp,
      show (prefixOps ++ [op]) ++ rest = prefixOps ++ op :: rest by simp] at remaining
    have next := Transition.op (s := (⟨⟨func, label, prefixOps.length⟩, fr, [], initial⟩ : State Reg))
      (Prog.fetch_op found atIndex) effect
    exact .head ⟨next.step_eq, List.nil_suffix⟩ remaining
  | call _ impossible _ _ _ => exact impossible.elim

private theorem emitOpsWith_length {ports : List PortTy} (argReg : ∀ {t}, Port ports t → Reg)
    (flow : Dataflow WordOp ports past sigs) :
    (emitOpsWith (fun p => argReg p) flow).length = sigs.length := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem emitOpsWith_steps {ports : List PortTy} (argReg : ∀ {t}, Port ports t → Reg)
    (separate : ∀ {t} (p : Port ports t) (i : Nat), argReg p ≠ .node i)
    (input : Tuple (Val model.value) ports) (flow : Dataflow WordOp ports [] sigs)
    (fr : Frame Reg) (mem : Memory) (prog : Prog Reg) (func label : Nat) (block : Block Reg)
    (found : prog.block? func label = some block) (code : block.ops = emitOpsWith (fun p => argReg p) flow)
    (agree : ∀ {t} (p : Port ports t), fr.get (argReg p) = some (encodeValue t (input.get p))) :
    ∃ ready, StepsNWithin prog [] sigs.length ⟨⟨func, label, 0⟩, fr, [], mem⟩
      ⟨⟨func, label, sigs.length⟩, ready, [], mem⟩ ∧
      ∀ {t} (wire : Origin ports (extend [] sigs) t),
        ready.get (registerWith (fun p => argReg p) wire) =
          some (encodeValue t (read model wire input (flow.eval model input PUnit.unit))) := by
  obtain ⟨ready, executed, ha, hl⟩ :=
    simulate_ops (fun p => argReg p) (fun p i => separate p i) (fun _ _ _ _ _ => False)
      input mem flow fr PUnit.unit agree trivial
  refine ⟨ready, ?_, fun wire => read_origin ha hl wire⟩
  simpa only [emitOpsWith_length, List.nil_append, List.length_nil] using counted_steps found executed [] code

private theorem arm_block (g : WordDiamond sigs) (p : Projection) :
    (lowerFunc g).block? (armLabel p) = some (armBlock g p) := by
  cases p <;> rfl

private theorem exec_arm (g : WordDiamond sigs) (p : Projection) (fr : Frame Reg)
    (mem : Memory) (value : Word) (h : fr.get (incoming g p) = some value) :
    Func.Exec (lower g).oracle (lowerFunc g) (armLabel p) fr mem (.returned [value] mem) := by
  refine .jump (vals := [value]) (fr₂ := fr.set .phi value)
    (arm_block g p) .nil rfl ?_ rfl rfl ?_
  · simp [Frame.readAll, h]
  · refine .ret rfl .nil rfl ?_
    simp [Frame.readAll]

private theorem branch_label (b : Bool) :
    (if ofBool b = 0 then armLabel .onFalse else armLabel .onTrue) =
      armLabel (Projection.ofBool b) := by
  cases b <;> decide

private theorem exec_entry (g : WordDiamond sigs) (x y : Word) (mem : Memory) :
    Func.Exec (lower g).oracle (lowerFunc g) 0 (initialFrame x y) mem
      (.returned [g.denote model (entry x y)] mem) := by
  obtain ⟨fr, steps, ha, hl⟩ :=
    simulate_ops (fun p => .arg (portIndex p)) (fun _ _ => by simp) (lower g).oracle
      (entry x y) mem g.dataflow (initialFrame x y) PUnit.unit (initial_args x y) trivial
  let xs := g.dataflow.eval model (entry x y) PUnit.unit
  let b := (read model g.predicate (entry x y) xs).down
  let p := Projection.ofBool b
  have cond := read_origin ha hl g.predicate
  have arm := exec_arm g p fr mem _
    (read_origin ha hl (g.phi.operand (g.phi.merge.slot p)))
  refine .cond (b := entryBlock g) (bt := armBlock g p) (x := ofBool b) (vals := []) (fr₂ := fr)
    rfl steps rfl cond ?_ ?_ rfl ?_
  · simp [Frame.readAll]
  · rw [branch_label]
    exact arm_block g p
  · rw [branch_label]
    exact arm

private theorem emitted_returns (g : WordDiamond sigs) (x y : Word) (mem : Memory) :
    (lower g).oracle 0 [x, y] mem [g.denote model (entry x y)] mem :=
  (Func.exec_returned_iff_oracle (p := lower g) (f := 0) (fn := lowerFunc g)
    (b := entryBlock g) (args := [x, y]) (fr := initialFrame x y) rfl rfl rfl).mp (exec_entry g x y mem)

theorem lower_returns_iff (g : WordDiamond sigs) (x y : Word) (initial final : Memory)
    (returned : List Word) :
    (lower g).oracle 0 [x, y] initial returned final ↔
      ∃ value : Word, g.Returns model (entry x y) value ∧ returned = [value] ∧ final = initial := by
  have expected := emitted_returns g x y initial
  constructor
  · intro actual
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic (lower g) 0 [x, y] initial _ _ _ _ actual expected
    exact ⟨g.denote model (entry x y), (g.returns_iff_denote model _ _).mpr rfl, valuesEq, memEq⟩
  · rintro ⟨value, h, rfl, rfl⟩
    rw [← (g.returns_iff_denote model _ _).mp h]
    exact expected

theorem lower_forward (g : WordDiamond sigs) {source target : Nat}
    (h : target ∈ (lowerFunc g).succ source) : source < target := by
  rcases source with _ | _ | _ | _ | source
  all_goals simp [Func.succ, Func.block?, lowerFunc, entryBlock, armBlock, joinBlock, armLabel,
    Silmaril.Machine.RTL.SSA.Term.successors] at h
  all_goals omega

end Silmaril.Machine.SeaOfNodes.Diamond.RTL.Proofs
