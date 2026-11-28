module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Val ValueSort dataPorts)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.Builder.Preheader (Native)
open GVN.Cyclic.Iteration.Preheader (normalize normalize_entry normalize_evalBackedges)
open GVN.Cyclic.Iteration.Preheader.MLIR
open Pure.SubZero (Opcode model word)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (Op evalOp)
open Silmaril.MLIR.Arith (Env)

private abbrev cfModel := Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.model

private theorem cast_trans {A : Type} (F : A → Type) {x y z : A}
    (first : x = y) (second : y = z) (data : F x) :
    second ▸ (first ▸ data : F y) = (first.trans second) ▸ data := by
  cases first
  cases second
  rfl

section Wires

variable {args outs : List (Diamond.Ty Unit)} {past sigs : List (List (Diamond.Ty Unit))}
variable {t : Diamond.Ty Unit}

private def locals : {past : List (List (Diamond.Ty Unit))} →
    Locals (Val model.value) past → Locals (Val Word) (bindings past)
  | [], _ => PUnit.unit
  | _ :: _, env => (values env.1, locals env.2)

private theorem cast_tuple_get {ps qs : List (Diamond.Ty Silmaril.MLIR.Arith.Width)} (eq : ps = qs)
    (vals : Tuple (Val Word) ps) {s : Diamond.Ty Silmaril.MLIR.Arith.Width} (p : Port ps s) :
    (eq ▸ vals).get (eq ▸ p) = vals.get p := by
  cases eq
  rfl

private theorem values_get (input : Tuple (Val model.value) args) (p : Port args t) :
    (values input).get (port p) = value (input.get p) := by
  induction p with
  | head => cases input; rfl
  | tail _ ih => cases input with | cons _ tail => exact ih tail

private theorem locals_get (env : Locals (Val model.value) past) (i : Fin past.length) :
    (locals env).get (index i) = slot_eq i ▸ values (env.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih env.2 j

private theorem origin_read (input : Tuple (Val model.value) args) (env : Locals (Val model.value) past)
    (wire : Origin args past t) :
    Diamond.read cfModel (origin wire) (values input) (locals env) = value (Diamond.read model wire input env) := by
  cases wire with
  | arg p => exact values_get input p
  | output i p =>
    change ((locals env).get (index i)).get (slot_eq i ▸ port p) = value ((env.get i).get p)
    rw [locals_get, cast_tuple_get]
    exact values_get (env.get i) p

private theorem wires_read (input : Tuple (Val model.value) args) (env : Locals (Val model.value) past)
    (packet : Wires args past outs) :
    (wires packet).read (values input) (locals env) = values (packet.read input env) := by
  induction packet with
  | nil => rfl
  | cons wire tail ih => exact congrArg₂ Tuple.cons (origin_read input env wire) ih

private theorem values_append {front back : List (Diamond.Ty Unit)}
    (first : Tuple (Val model.value) front) (last : Tuple (Val model.value) back) :
    List.map_append (f := retargetTy) (l₁ := front) (l₂ := back) ▸ values (Loop.appendTuple last first) =
      Loop.appendTuple (values last) (values first) := by
  induction first with
  | nil => rfl
  | @cons t ps val rest ih =>
    have cast_cons {x y : List (Diamond.Ty Silmaril.MLIR.Arith.Width)} (eq : x = y)
        (tail : Tuple (Val Word) x) :
        congrArg (List.cons (retargetTy t)) eq ▸ Tuple.cons (value val) tail =
          Tuple.cons (value val) (eq ▸ tail) := by
      cases eq
      rfl
    change (congrArg (List.cons (retargetTy t)) (List.map_append (f := retargetTy) (l₁ := ps) (l₂ := back)) ▸
      Tuple.cons (value val) (values (Loop.appendTuple last rest))) = _
    rw [cast_cons (List.map_append (f := retargetTy) (l₁ := ps) (l₂ := back)), ih]
    rfl

private theorem locals_snoc {head : List (Diamond.Ty Unit)}
    (env : Locals (Val model.value) past) (next : Tuple (Val model.value) head) :
    List.map_append (f := ports) (l₁ := past) (l₂ := [head]) ▸ locals (env.snoc next) = (locals env).snoc (values next) := by
  induction past with
  | nil => rfl
  | cons head tail ih =>
    have cast_pair {x y : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))} (eq : x = y)
        (front : Tuple (Val Word) (ports head)) (rest : Locals (Val Word) x) :
        congrArg (List.cons (ports head)) eq ▸ (show Locals (Val Word) (ports head :: x) from (front, rest)) =
          (show Locals (Val Word) (ports head :: y) from (front, eq ▸ rest)) := by
      cases eq
      rfl
    change (congrArg (List.cons (ports head)) (List.map_append (f := ports) (l₁ := tail) (l₂ := [_])) ▸
      (show Locals (Val Word) (ports head :: bindings (tail ++ [_])) from
        (values env.1, locals (env.2.snoc next)))) = _
    rw [cast_pair (List.map_append (f := ports) (l₁ := tail) (l₂ := [_])), ih]
    rfl

private theorem reindex_ports_read {a p q : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {past : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))} (eq : p = q)
    (packet : Wires a past p) (entry : Tuple (Val Word) a) (state : Locals (Val Word) past) :
    (eq ▸ packet).read entry state = eq ▸ packet.read entry state := by
  cases eq
  rfl

private theorem reindex_origin_read {a b : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {xs ys : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))} {t : Diamond.Ty Silmaril.MLIR.Arith.Width}
    (argsEq : a = b) (scopeEq : xs = ys)
    (wire : Origin a xs t) (entry : Tuple (Val Word) a) (state : Locals (Val Word) xs) :
    Diamond.read cfModel (argsEq ▸ scopeEq ▸ wire) (argsEq ▸ entry) (scopeEq ▸ state) =
      Diamond.read cfModel wire entry state := by
  cases argsEq
  cases scopeEq
  rfl

end Wires

section Flow

variable {args : List (Diamond.Ty Unit)} {past sigs : List (List (Diamond.Ty Unit))}

private theorem opcode_sound {ins : List (ValueSort Unit)} {out : ValueSort Unit}
    {op : Opcode ins out} {mapped : Op (ins.map retargetSort) (retargetSort out)}
    (fit : opcode? op = some mapped) (args : Tuple (Val model.value) (dataPorts ins)) :
    cfModel.run mapped (sourceInput args) = value (t := .value out) (model.run op args) := by
  cases op with
  | sub => cases fit
  | literal =>
    cases Option.some.inj fit
    cases args
    rfl
  | add | mul =>
    cases Option.some.inj fit
    cases args with | cons first rest =>
    cases rest with | cons second rest =>
    cases rest
    rfl

private theorem eval_scope_cast {args : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {x y sigs : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))} (eq : x = y)
    (flow : Dataflow Op args x sigs) (input : Tuple (Val Word) args) (state : Locals (Val Word) x) :
    (eq ▸ flow).eval cfModel input (eq ▸ state) =
      congrArg (fun scope => extend scope sigs) eq ▸ flow.eval cfModel input state := by
  cases eq
  rfl

private theorem eval_args_cast {args args' : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {past sigs : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))} (eq : args = args')
    (flow : Dataflow Op args past sigs) (input : Tuple (Val Word) args) (state : Locals (Val Word) past) :
    (eq ▸ flow).eval cfModel (eq ▸ input) state = flow.eval cfModel input state := by
  cases eq
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem flow_eval (flow : Dataflow Opcode args past sigs)
    {mapped : Dataflow Op (ports args) (bindings past) (bindings sigs)} (fit : flow? flow = some mapped)
    (input : Tuple (Val model.value) args) (state : Locals (Val model.value) past) :
    mapped.eval cfModel (values input) (locals state) =
      bindings_extend past sigs ▸ locals (flow.eval model input state) := by
  induction flow with
  | nil =>
    cases Option.some.inj fit
    rfl
  | @cons scope sigs ins out op packet rest ih =>
    obtain ⟨converted, fitOp, next⟩ := Option.bind_eq_some_iff.mp fit
    obtain ⟨tail, fitTail, eq⟩ := Option.bind_eq_some_iff.mp next
    cases Option.some.inj eq
    simp only [Diamond.Dataflow.eval]
    rw [reindex_ports_read, wires_read]
    have runSound : cfModel.run converted (ports_data ins ▸ values (packet.read input state)) =
        value (t := .value out) (model.run op (packet.read input state)) :=
      opcode_sound fitOp (packet.read input state)
    let castTail : Dataflow Op (ports args) (bindings scope ++ [[.value (retargetSort out)]]) (bindings sigs) :=
      (show bindings (scope ++ [[.value out]]) = bindings scope ++ [[.value (retargetSort out)]]
        from List.map_append ..) ▸ tail
    change castTail.eval cfModel (values input)
      ((locals state).snoc (.cons (cfModel.run converted (ports_data ins ▸ values (packet.read input state))) .nil)) = _
    rw [runSound]
    let newValue : Tuple (Val model.value) [.value out] :=
      .cons (model.run op (packet.read input state)) .nil
    let nextState := state.snoc newValue
    have bindingEq : bindings (scope ++ [[.value out]]) =
        bindings scope ++ [[.value (retargetSort out)]] := List.map_append ..
    change ((bindingEq ▸ tail) : Dataflow Op (ports args) _ _).eval cfModel (values input)
      ((locals state).snoc (values newValue)) =
        bindings_extend scope ([.value out] :: sigs) ▸ locals (rest.eval model input nextState)
    rw [← locals_snoc state newValue, eval_scope_cast, ih fitTail nextState]
    rw [cast_trans]

end Flow

section Loop

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Diamond.Ty Unit))}
variable {g : Native inputs carried entrySigs headerSigs word}
variable {target : Retargeted inputs carried entrySigs headerSigs}

private theorem cast_append {a b c d : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    (left : a = b) (right : c = d) (front : Tuple (Val Word) a) (back : Tuple (Val Word) c) :
    (show Tuple (Val Word) (b ++ d) from (show a ++ c = b ++ d from congrArg₂ List.append left right) ▸ Loop.appendTuple back front) =
      Loop.appendTuple (right ▸ back) (left ▸ front) := by
  cases left
  cases right
  rfl

private theorem sourceInput_append (input : Inputs model inputs) (old : Inputs model carried) :
    (show Tuple (Val Word) (Loop.headerPorts (inputs.map retargetSort) (carried.map retargetSort)) from
      header_ports inputs carried ▸ values (Loop.appendTuple old input)) =
      Loop.appendTuple (sourceInput old) (sourceInput input) := by
  unfold sourceInput
  rw [← cast_append, ← values_append, cast_trans]

private theorem read_packet {a b p q : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {xs ys : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))}
    (argsEq : a = b) (scopeEq : xs = ys) (outputEq : p = q)
    (packet : Wires a xs p) (entry : Tuple (Val Word) a) (state : Locals (Val Word) xs) :
    (show Wires b ys q from argsEq ▸ scopeEq ▸ outputEq ▸ packet).read (argsEq ▸ entry) (scopeEq ▸ state) =
      outputEq ▸ packet.read entry state := by
  cases argsEq
  cases scopeEq
  cases outputEq
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem retarget_initial (fit : retarget? g = some target) (input : Inputs model inputs) :
    target.initial Loop.MLIR.CF.model (sourceInput input) = sourceInput (g.initial model input) := by
  obtain ⟨pre, fitPre, next⟩ := Option.bind_eq_some_iff.mp fit
  obtain ⟨header, _, out⟩ := Option.bind_eq_some_iff.mp next
  cases Option.some.inj out
  simp only [Loop.Graph.initial, Loop.Graph.latch, sourceInput, Loop.Incoming.select]
  have pre_eval := flow_eval _ fitPre input PUnit.unit
  change pre.eval cfModel (values input) PUnit.unit = _ at pre_eval
  rw [eval_args_cast, pre_eval, read_packet, wires_read]

set_option backward.isDefEq.respectTransparency false in
theorem retarget_step (fit : retarget? g = some target) (input : Inputs model inputs) (old : Inputs model carried) :
    target.step Loop.MLIR.CF.model (sourceInput input) (sourceInput old) = (g.step model input old).map id sourceInput := by
  obtain ⟨pre, _, next⟩ := Option.bind_eq_some_iff.mp fit
  obtain ⟨header, fitHeader, out⟩ := Option.bind_eq_some_iff.mp next
  cases Option.some.inj out
  simp only [Loop.Graph.step, Loop.Graph.latch, Loop.Incoming.select]
  have header_eval := flow_eval _ fitHeader (Loop.appendTuple old input) PUnit.unit
  change header.eval cfModel (values (Loop.appendTuple old input)) PUnit.unit = _ at header_eval
  rw [← sourceInput_append, eval_args_cast, header_eval, reindex_origin_read,
    origin_read, reindex_origin_read, origin_read, read_packet, wires_read]
  let flag := Diamond.read model g.predicate (Loop.appendTuple old input)
    (g.header.eval model (Loop.appendTuple old input) PUnit.unit)
  change (if flag.down then _ else _) = Sum.map id sourceInput (if flag.down then _ else _)
  cases flag.down <;> rfl

private theorem retarget_evalFrom (fit : retarget? g = some target) (input : Inputs model inputs)
    (budget : Nat) (old : Inputs model carried) :
    target.evalFrom cfModel (sourceInput input) budget (sourceInput old) = g.evalFrom model input budget old := by
  induction budget generalizing old with
  | zero =>
    simp only [Loop.Graph.evalFrom, retarget_step fit]
    cases g.step model input old <;> rfl
  | succ fuel ih =>
    simp only [Loop.Graph.evalFrom, retarget_step fit]
    cases g.step model input old with
    | inl => rfl
    | inr next => exact ih next

theorem retarget_eval (fit : retarget? g = some target) (input : Inputs model inputs) (budget : Nat) :
    target.evalBackedges Loop.MLIR.CF.model budget (sourceInput input) = g.evalBackedges model budget input := by
  simp only [Loop.Graph.evalBackedges, retarget_initial fit]
  exact retarget_evalFrom fit input budget (g.initial model input)

end Loop

section Emit

variable {inputs carried : List (ValueSort Unit)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Unit))}
variable {g : Native inputs carried entrySigs headerSigs word}
variable {source normalized : Artifact inputs carried}

theorem emit_entry_frame (fit : emit? g = some source) (input : Inputs model inputs) :
    source.entry.eval evalOp (fun term env => term.eval env) (inputEnv input) =
      .inl ⟨.header, inputEnv (g.initial model input)⟩ := by
  obtain ⟨target, linked, rfl⟩ := Option.map_eq_some_iff.mp fit
  have frame := Loop.MLIR.CF.Mixed.lower_entry_frame target (sourceInput input)
  rw [retarget_initial linked] at frame
  exact frame

set_option backward.isDefEq.respectTransparency false in
theorem emit_run (fit : emit? g = some source) (input : Inputs model inputs) (budget : Nat) :
    source.run evalOp (budget + 3) (inputEnv input) =
      (g.evalBackedges model budget input).map (fun bits : BitVec 64 => Env.cons (w := i64) bits .nil) := by
  obtain ⟨target, linked, rfl⟩ := Option.map_eq_some_iff.mp fit
  have run := Loop.MLIR.CF.Mixed.lower_run target (sourceInput input) budget
  rw [retarget_eval linked] at run
  exact run

private theorem emit_short (fit : emit? g = some source) (input : Inputs model inputs)
    (fuel : Nat) (short : fuel < 3) :
    source.run evalOp fuel (inputEnv input) = none := by
  obtain ⟨target, _, rfl⟩ := Option.map_eq_some_iff.mp fit
  exact Loop.MLIR.CF.Mixed.lower_run_short target (sourceInput input) fuel short

set_option backward.isDefEq.respectTransparency false in
theorem emit_returns_iff (fit : emit? g = some source) (input : Inputs model inputs)
    (bits : BitVec 64) :
    (∃ fuel, source.run evalOp fuel (inputEnv input) = some (.cons bits .nil)) ↔
      g.Returns model input bits := by
  rw [Loop.Graph.returns_iff_evalBackedges]
  constructor
  · rintro ⟨fuel, returned⟩
    by_cases short : fuel < 3
    · rw [emit_short fit input fuel short] at returned
      contradiction
    · obtain ⟨budget, rfl⟩ : ∃ budget, fuel = budget + 3 := ⟨fuel - 3, by omega⟩
      rw [emit_run fit input budget] at returned
      obtain ⟨value, eval, eq⟩ := Option.map_eq_some_iff.mp returned
      cases eq
      exact ⟨budget, eval⟩
  · rintro ⟨budget, returned⟩
    exact ⟨budget + 3, by rw [emit_run fit input budget, returned]; rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem emit_normalized_entry_eq (original : emit? g = some source)
    (edited : emitNormalized? g = some normalized) : normalized.entry = source.entry := by
  have same := normalize_entry g
  obtain ⟨sourceTarget, linkedSource, rfl⟩ := Option.map_eq_some_iff.mp original
  obtain ⟨nativeTarget, linkedNative, eq⟩ := Option.map_eq_some_iff.mp edited
  subst normalized
  obtain ⟨sourcePre, fitSourcePre, sourceNext⟩ := Option.bind_eq_some_iff.mp linkedSource
  obtain ⟨_, _, sourceOut⟩ := Option.bind_eq_some_iff.mp sourceNext
  obtain ⟨nativePre, fitNativePre, nativeNext⟩ := Option.bind_eq_some_iff.mp linkedNative
  obtain ⟨_, _, nativeOut⟩ := Option.bind_eq_some_iff.mp nativeNext
  cases Option.some.inj sourceOut
  cases Option.some.inj nativeOut
  have samePre := same.1
  rw [samePre, fitSourcePre] at fitNativePre
  cases Option.some.inj fitNativePre
  simp only [Loop.MLIR.CF.Mixed.lower, Loop.Incoming.select]
  rw [same.2]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem emit_normalized_run_eq (original : emit? g = some source)
    (edited : emitNormalized? g = some normalized) (input : Inputs model inputs) (fuel : Nat) :
    normalized.run evalOp fuel (inputEnv input) = source.run evalOp fuel (inputEnv input) := by
  by_cases short : fuel < 3
  · exact (emit_short edited input fuel short).trans (emit_short original input fuel short).symm
  · obtain ⟨budget, rfl⟩ : ∃ budget, fuel = budget + 3 := ⟨fuel - 3, by omega⟩
    rw [emit_run edited input budget, emit_run original input budget, normalize_evalBackedges]

end Emit

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR
