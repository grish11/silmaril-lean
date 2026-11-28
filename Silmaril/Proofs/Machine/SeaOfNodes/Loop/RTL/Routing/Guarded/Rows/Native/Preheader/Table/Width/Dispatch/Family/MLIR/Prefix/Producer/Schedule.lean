module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Thms
public import Silmaril.SSA.SeaOfNodes.MLIR.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Proofs

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp model)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Port Origin Tuple Wires Locals extend)

abbrev CFVal := Val Loop.MLIR.CF.model.value

def value : {t : PortTy} → Val model.value t → CFVal (portType t)
  | .value (.data _), bits => bits
  | .value .predicate, b => b
  | .control _, control => control
  | .state s, _ => nomatch s

def values {ps : List PortTy} : Tuple (Val model.value) ps → Tuple CFVal (ports ps)
  | .nil => .nil
  | .cons x tail => .cons (value x) (values tail)

def locals : {past : List (List PortTy)} → Locals (Val model.value) past → Locals CFVal (table past)
  | [], _ => PUnit.unit
  | _ :: _, ls => ⟨values ls.1, locals ls.2⟩

private theorem port_get {ps : List PortTy} {t : PortTy} (p : Port ps t) (vs : Tuple (Val model.value) ps) :
    (values vs).get (port p) = value (vs.get p) := by
  induction p with
  | head => cases vs; rfl
  | tail p ih => cases vs with | cons _ tail => exact ih tail

private theorem result_get {past : List (List PortTy)} {t : PortTy}
    (i : Fin past.length) (p : Port past[i] t) (ls : Locals (Val model.value) past) :
    ((locals ls).get (index i)).get (resultPort i p) = value ((ls.get i).get p) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i p
    · intro p
      exact port_get p ls.1
    · intro p
      exact ih j p ls.2

theorem origin_read {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (wire : Origin args past t) (input : Tuple (Val model.value) args) (ls : Locals (Val model.value) past) :
    Diamond.read Loop.MLIR.CF.model (origin wire) (values input) (locals ls) =
      value (Diamond.read model wire input ls) := by
  cases wire with
  | arg p => exact port_get p input
  | output i p => exact result_get i p ls

private theorem column_read {args outs : List PortTy} {past : List (List PortTy)}
    (wires : Wires args past outs) (input : Tuple (Val model.value) args) (ls : Locals (Val model.value) past) :
    (column wires).read (values input) (locals ls) = values (wires.read input ls) := by
  induction wires with
  | nil => rfl
  | cons wire tail ih =>
    exact congrArg₂ Tuple.cons (origin_read wire input ls) ih

private theorem pair_heq {α β γ : Type} (head : α) {l : β} {r : γ} (h : HEq l r) :
    HEq (head, l) (head, r) := by
  cases h
  rfl

private theorem snoc_heq {past : List (List PortTy)} {row : List PortTy}
    (ls : Locals (Val model.value) past) (vs : Tuple (Val model.value) row) :
    HEq (locals (ls.snoc vs)) ((locals ls).snoc (values vs)) := by
  induction past with
  | nil => rfl
  | cons _ past ih =>
    change HEq (values ls.1, locals (ls.2.snoc vs)) (values ls.1, (locals ls.2).snoc (values vs))
    exact pair_heq _ (ih ls.2)

private theorem read_cast {args source dest : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {past : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))}
    (h : source = dest) (wires : Wires args past source)
    (input : Tuple CFVal args) (ls : Locals CFVal past) :
    (h ▸ wires : Wires args past dest).read input ls = h ▸ wires.read input ls := by cases h; rfl

private theorem opcode_eval {ins : List (ValueSort Unit)} {out : ValueSort Unit}
    (op : WordOp ins out) (cf : Loop.MLIR.CF.Op (ins.map sort) (sort out))
    (ok : opcode op = some cf) (input : Tuple (Val model.value) (dataPorts ins)) :
    Loop.MLIR.CF.model.run cf (ports_data ins ▸ values input) =
      value (t := .value out) (model.run op input) := by
  cases op <;> cases ok
  · cases input; rfl
  all_goals
    cases input with | cons x tail =>
      cases tail with | cons y tail =>
        cases tail
        rfl

private theorem eval_past_cast {args : List (Diamond.Ty Silmaril.MLIR.Arith.Width)}
    {before after rows : List (List (Diamond.Ty Silmaril.MLIR.Arith.Width))}
    (same : before = after) (d : Dataflow Loop.MLIR.CF.Op args before rows)
    (input : Tuple CFVal args) (left : Locals CFVal before) (right : Locals CFVal after)
    (h : HEq left right) :
    HEq (d.eval Loop.MLIR.CF.model input left)
      ((same ▸ d : Dataflow Loop.MLIR.CF.Op args after rows).eval Loop.MLIR.CF.model input right) := by
  cases same
  cases eq_of_heq h
  rfl

theorem flow_eval {args : List PortTy} {past sigs : List (List PortTy)}
    (d : Dataflow WordOp args past sigs) (cf : Dataflow Loop.MLIR.CF.Op (ports args) (table past) (table sigs))
    (ok : flow d = some cf) (input : Tuple (Val model.value) args) (ls : Locals (Val model.value) past) :
    HEq (cf.eval Loop.MLIR.CF.model (values input) (locals ls))
      (locals (d.eval model input ls)) := by
  induction d with
  | nil => cases ok; rfl
  | @cons past sigs ins out op wires tail ih =>
    simp only [flow] at ok
    obtain ⟨target, hitOp, ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨suffix, hitTail, eq⟩ := Option.bind_eq_some_iff.mp ok
    cases eq
    let inputs := wires.read input ls
    let produced := Tuple.cons (F := Val model.value) (t := Silmaril.SSA.RVSDG.PortType.value out)
      (model.run op inputs) .nil
    have operandEq : (ports_data ins ▸ column wires :
        Wires (ports args) (table past) (dataPorts (ins.map sort))).read (values input) (locals ls) =
        ports_data ins ▸ values inputs := by
      rw [read_cast, column_read]
    have newNode := opcode_eval op target hitOp inputs
    have nextEq : HEq (locals (ls.snoc produced))
        ((locals ls).snoc (Tuple.cons (F := CFVal) (t := Silmaril.SSA.RVSDG.PortType.value (sort out)) (Loop.MLIR.CF.model.run target
          ((ports_data ins ▸ column wires :
            Wires (ports args) (table past) (dataPorts (ins.map sort))).read (values input) (locals ls))) .nil)) := by
      rw [operandEq, newNode]
      exact snoc_heq ls produced
    exact (eval_past_cast (table_snoc past [.value out]) suffix (values input) _ _ nextEq).symm.trans
      (ih suffix hitTail (ls.snoc produced))

open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.MLIR (sourceInputs)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)

private theorem cons_heq {Ty : Type} {F : Ty → Type} {xs ys : List Ty} {t : Ty}
    (x : F t) {a : Tuple F xs} {b : Tuple F ys} (same : xs = ys) (h : HEq a b) :
    HEq (Tuple.cons x a) (Tuple.cons x b) := by
  cases same
  cases eq_of_heq h
  rfl

private theorem words_heq {n : Nat} (words : WordTuple n) :
    HEq (values words) (sourceInputs (wordEnv words)) := by
  induction n with
  | zero => cases words; rfl
  | succ n ih =>
    cases words with
    | cons x rest =>
      exact cons_heq (F := CFVal) (t := .value (.data i64)) x (wordPorts_eq n) (ih rest)

private theorem append_values {xs ys : List PortTy}
    (first : Tuple (Val model.value) xs) (last : Tuple (Val model.value) ys) :
    HEq (values (appendTuple last first)) (appendTuple (values last) (values first)) := by
  induction first with
  | nil => rfl
  | @cons t ts x rest ih =>
    exact cons_heq (value x) (List.map_append (f := portType) (l₁ := ts) (l₂ := ys)) ih

private theorem append_heq {xs xs' ys ys' : List (Diamond.Ty Width)}
    (hx : xs = xs') (hy : ys = ys') {x : Tuple CFVal xs} {x' : Tuple CFVal xs'}
    {y : Tuple CFVal ys} {y' : Tuple CFVal ys'} (ex : HEq x x') (ey : HEq y y') :
    HEq (appendTuple y x) (appendTuple y' x') := by
  cases hx
  cases hy
  cases eq_of_heq ex
  cases eq_of_heq ey
  rfl

private theorem header_args {captures bank : Nat} (input : WordTuple captures) (carried : WordTuple bank) :
    HEq (values (appendTuple carried input))
      (appendTuple (sourceInputs (wordEnv carried)) (sourceInputs (wordEnv input))) :=
  (append_values input carried).trans
    (append_heq (wordPorts_eq captures) (wordPorts_eq bank) (words_heq input) (words_heq carried))

private theorem eval_args_cast {args args' : List (Diamond.Ty Width)} {sigs : List (List (Diamond.Ty Width))}
    (same : args = args') (d : Dataflow Loop.MLIR.CF.Op args [] sigs)
    {input : Tuple CFVal args} {input' : Tuple CFVal args'} (h : HEq input input') :
    d.eval Loop.MLIR.CF.model input PUnit.unit =
      (same ▸ d : Dataflow Loop.MLIR.CF.Op args' [] sigs).eval Loop.MLIR.CF.model input' PUnit.unit := by
  cases same
  cases eq_of_heq h
  rfl

private theorem read_origin_cast {args args' : List (Diamond.Ty Width)}
    {past past' : List (List (Diamond.Ty Width))} {t : Diamond.Ty Width}
    (argsEq : args = args') (pastEq : past = past') (wire : Origin args past t)
    {input : Tuple CFVal args} {input' : Tuple CFVal args'} {ls : Locals CFVal past}
    {ls' : Locals CFVal past'} (inputs : HEq input input') (evaluated : HEq ls ls') :
    Diamond.read Loop.MLIR.CF.model wire input ls =
      Diamond.read Loop.MLIR.CF.model (argsEq ▸ pastEq ▸ wire : Origin args' past' t) input' ls' := by
  cases argsEq
  cases pastEq
  cases eq_of_heq inputs
  cases eq_of_heq evaluated
  rfl

private theorem graph_header {captures bank : Nat} {entrySigs sigs : List (List PortTy)}
    {src : Width.Source captures bank entrySigs sigs} {g : MLIR.Program captures bank (table entrySigs) (table sigs)}
    (ok : graph src = some g) :
    headerFlow src = some g.header ∧ g.predicate = headerOrigin src.predicate ∧
      g.result = headerOrigin src.result := by
  obtain ⟨entry, _, ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨header, hit, eq⟩ := Option.bind_eq_some_iff.mp ok
  cases eq
  exact ⟨hit, rfl, rfl⟩

theorem header_read {captures bank : Nat} {entrySigs sigs : List (List PortTy)}
    {src : Width.Source captures bank entrySigs sigs} {g : MLIR.Program captures bank (table entrySigs) (table sigs)}
    (ok : graph src = some g) (input : WordTuple captures) (carried : WordTuple bank)
    {t : PortTy} (wire : Silmaril.SSA.RVSDG.Origin (wordPorts captures ++ wordPorts bank)
      (extend [] sigs) t) :
    let args := appendTuple (sourceInputs (wordEnv carried)) (sourceInputs (wordEnv input))
    let nativeArgs := appendTuple carried input
    Diamond.read Loop.MLIR.CF.model (headerOrigin wire) args (g.header.eval Loop.MLIR.CF.model args PUnit.unit) =
      value (Diamond.read model wire nativeArgs (src.header.eval model nativeArgs PUnit.unit)) := by
  have ⟨built, _⟩ := graph_header ok
  obtain ⟨cf, hit, eq⟩ := Option.map_eq_some_iff.mp built
  have args := header_args input carried
  have h := (flow_eval src.header cf hit (appendTuple carried input) PUnit.unit).symm.trans
    (heq_of_eq (eval_args_cast (headerPorts_eq captures bank) cf args))
  rw [eq] at h
  exact (read_origin_cast (headerPorts_eq captures bank) (table_extend [] sigs)
    (origin wire) args h).symm.trans (origin_read wire _ _)

private theorem readLive_get {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    (input : Tuple CFVal args) (ls : Locals CFVal past)
    (wires : List (Origin args past (.value (.data i64)))) {Γ : List Width} (extra : Env Γ)
    (i : Fin wires.length) :
    ((readLive input ls wires).append extra).get (argAt wires.length i) =
      Diamond.read Loop.MLIR.CF.model wires[i] input ls := by
  induction wires with
  | nil => exact i.elim0
  | cons _ tail ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih j

theorem header_match {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
    {g : MLIR.Program new old (table entrySigs) (table sigs)}
    (origins : List (HeaderWord new old sigs))
    (sys : Setup mapping source g (live origins))
    (origin_eq : ∀ i, sys.origin i = liveOrigin origins i)
    (ok : graph (mapCaptures mapping source).primary = some g)
    (input : WordTuple new) (carried : WordTuple old) : HeaderMatch sys input carried := by
  refine ⟨?_, ?_⟩
  · rw [(graph_header ok).2.1]
    exact congrArg ULift.down (header_read ok input carried _)
  · intro i
    unfold livePacket
    rw [readLive_get, origin_eq]
    have selected : (live origins)[i.cast (List.length_map ..)] = headerOrigin (liveOrigin origins i) := by
      change (origins.map headerOrigin)[i.val]'_ = _
      exact List.getElem_map headerOrigin
    rw [selected]
    exact header_read ok input carried _

private theorem port_index {ps : List PortTy} {t : PortTy} (p : Port ps t) :
    (port p).index = p.index := by
  induction p with
  | head => rfl
  | tail p ih => exact congrArg (· + 1) ih

private theorem index_cast {Ty : Type} {xs ys : List Ty} {t : Ty}
    (same : xs = ys) (p : Port xs t) : (same ▸ p : Port ys t).index = p.index := by
  cases same
  rfl

private theorem origin_address {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (wire : Origin args past t) : (origin wire).address = wire.address := by
  cases wire with
  | arg p => exact congrArg Silmaril.SSA.RVSDG.Address.arg (port_index p)
  | output i p =>
    exact congrArg (Silmaril.SSA.RVSDG.Address.output i.val) ((index_cast _ _).trans (port_index p))

private theorem address_cast {Ty : Type} {args args' : List Ty} {past past' : List (List Ty)} {t : Ty}
    (argsEq : args = args') (pastEq : past = past') (wire : Origin args past t) :
    (argsEq ▸ pastEq ▸ wire : Origin args' past' t).address = wire.address := by
  cases argsEq
  cases pastEq
  rfl

theorem live_register {captures bank : Nat} {sigs : List (List PortTy)}
    (origins : List (HeaderWord captures bank sigs)) (i : Fin (liveRegs (live origins)).length) :
    register (liveOrigin origins i).address = (liveRegs (live origins))[i] := by
  change register (liveOrigin origins i).address =
    ((origins.map headerOrigin).map (fun wire => register (Origin.address wire)))[i.val]'i.isLt
  calc
    _ = register (headerOrigin (liveOrigin origins i)).address :=
      congrArg register ((address_cast _ _ _).trans (origin_address _)).symm
    _ = _ := ((List.getElem_map (fun wire => register (Origin.address wire))).trans
      (congrArg (fun wire => register (Origin.address wire)) (List.getElem_map headerOrigin))).symm

private theorem read_column_cast {args args' outs outs' : List (Diamond.Ty Width)}
    {past past' : List (List (Diamond.Ty Width))}
    (argsEq : args = args') (pastEq : past = past') (outsEq : outs = outs') (wires : Wires args past outs)
    {input : Tuple CFVal args} {input' : Tuple CFVal args'} {ls : Locals CFVal past}
    {ls' : Locals CFVal past'} (inputs : HEq input input') (evaluated : HEq ls ls') :
    HEq (wires.read input ls) ((argsEq ▸ pastEq ▸ outsEq ▸ wires : Wires args' past' outs').read input' ls') := by
  cases argsEq
  cases pastEq
  cases outsEq
  cases eq_of_heq inputs
  cases eq_of_heq evaluated
  rfl

private theorem translated_initial {captures bank : Nat} {entrySigs sigs : List (List PortTy)}
    {src : Width.Source captures bank entrySigs sigs} {g : MLIR.Program captures bank (table entrySigs) (table sigs)}
    (ok : graph src = some g) (input : WordTuple captures) :
    g.initial Loop.MLIR.CF.model (sourceInputs (wordEnv input)) =
      sourceInputs (wordEnv (src.initial model input)) := by
  obtain ⟨entry, hit, ok⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨_, _, eq⟩ := Option.bind_eq_some_iff.mp ok
  cases eq
  obtain ⟨cf, translated, eq⟩ := Option.map_eq_some_iff.mp hit
  cases eq
  have args := words_heq input
  have evaluated := (flow_eval src.preheader cf translated input PUnit.unit).symm.trans
    (heq_of_eq (eval_args_cast (wordPorts_eq captures) cf args))
  exact eq_of_heq ((read_column_cast (wordPorts_eq captures) (table_extend [] entrySigs)
      (wordPorts_eq bank) (column (src.phiInputs .entry)) args evaluated).symm.trans
    ((heq_of_eq (column_read (src.phiInputs .entry) input _)).trans (words_heq (src.initial model input))))

private theorem wordEnv_bankEnv {n : Nat} (words : WordTuple n) :
    Loop.MLIR.CF.Bank.bankEnv (sourceInputs (wordEnv words)) = wordEnv words := by
  induction n with
  | zero => cases words; rfl
  | succ n ih =>
    cases words with
    | cons x rest => exact congrArg (Env.cons (w := i64) x) (ih rest)

open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (Scope lowerCode lowerCode_eval inputs_agree)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)

theorem header_exit {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
    {g : MLIR.Program new old (table entrySigs) (table sigs)} {wires : Live new old (table sigs)}
    (sys : Setup mapping source g wires) (ok : graph (mapCaptures mapping source).primary = some g)
    (input : WordTuple new) (carried : WordTuple old) (returned : Silmaril.Machine.Lir.Word)
    {before ready : Silmaril.Machine.RTL.Frame Silmaril.Machine.SeaOfNodes.Diamond.RTL.Reg}
    {mem : Silmaril.Machine.Lir.Memory}
    (cut : Family.ExitCut (mapCaptures mapping source) sys.rtl input carried before ready mem returned) :
    ((sys.cf.block .header).eval evalOp (fun term env => term.eval env)
      ((wordEnv carried).append (wordEnv input))) = .inl ⟨.exit, .cons returned .nil⟩ := by
  have header := MLIR.header_frame g wires sys.plan (wordEnv input) (sourceInputs (wordEnv carried))
  rw [wordEnv_bankEnv] at header
  dsimp only at header
  let args := appendTuple (sourceInputs (wordEnv carried)) (sourceInputs (wordEnv input))
  let ls := g.header.eval Loop.MLIR.CF.model args PUnit.unit
  have zero : (Diamond.read Loop.MLIR.CF.model g.predicate args ls).down = false := by
    rw [(graph_header ok).2.1]
    exact (congrArg ULift.down (header_read ok input carried _)).trans cut.zero
  have result : Diamond.read Loop.MLIR.CF.model g.result args ls = returned := by
    rw [(graph_header ok).2.2]
    exact (header_read ok input carried _).trans cut.result_eq
  rw [zero, result] at header
  exact header

private theorem bankOperands_eval {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    {Δ widths : List Width} {scope : Scope args past Δ} {env : Env Δ}
    {input : Tuple CFVal args} {ls : Locals CFVal past} (agree : scope.Agrees env input ls)
    (wires : Wires args past (Diamond.dataPorts (Loop.MLIR.CF.inputSorts widths))) :
    (Loop.MLIR.CF.Bank.bankOperands scope wires).eval env =
      Loop.MLIR.CF.Bank.bankEnv (wires.read input ls) := by
  induction widths with
  | nil => rfl
  | cons _ rest ih =>
    cases wires with
    | cons wire tail => exact congrArg₂ Env.cons (agree.resolve wire) (ih tail)

theorem entry_frame {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
    {g : MLIR.Program new old (table entrySigs) (table sigs)} {wires : Live new old (table sigs)}
    (sys : Setup mapping source g wires) (ok : graph (mapCaptures mapping source).primary = some g)
    (input : WordTuple new) :
    sys.cf.entry.eval evalOp (fun term env => term.eval env) (wordEnv input) =
      .inl (headerFrame _ _ (source.primary.initial model (mapping.pull input))) := by
  have packed : Loop.MLIR.CF.Bank.bankEnv (g.initial Loop.MLIR.CF.model (sourceInputs (wordEnv input))) =
      wordEnv (source.primary.initial model (mapping.pull input)) :=
    (congrArg Loop.MLIR.CF.Bank.bankEnv (translated_initial ok input)).trans
      ((wordEnv_bankEnv _).trans (congrArg wordEnv (Table.Width.initial_mapCaptures mapping source.primary model input)))
  refine lowerCode_eval _ _ _ Loop.MLIR.CF.opcode_eval g.preheader _ _ _ PUnit.unit
    ⟨inputs_agree (wordEnv input), trivial⟩ _ _ _ ?_
  intro Δ scope env agree
  exact congrArg (fun args => Sum.inl (Silmaril.MLIR.CF.Frame.mk (Label.header (live := wires.length) (tests := tests)) args))
    ((bankOperands_eval agree (g.phiInputs .entry)).trans packed)

theorem prefix_correct {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
    {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
    {g : MLIR.Program new old (table entrySigs) (table sigs)} {wires : Live new old (table sigs)}
    (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Silmaril.Machine.Lir.Memory)
    (aligned : ∀ bank, HeaderMatch sys input bank) {slots : List (Fin (tests + 1))}
    {carried finish : WordTuple old}
    (taken : Feedbacks source (mapping.pull input) slots carried finish)
    (before : Silmaril.Machine.RTL.Frame Silmaril.Machine.SeaOfNodes.Diamond.RTL.Reg)
    (matched : ArgsMatch before (appendTuple carried input)) :
    ∃ after, Realized sys input mem slots carried before finish after := by
  have admitted : Admitted sys input slots carried finish := by
    clear matched before
    induction taken with
    | stop bank => exact .stop bank
    | visit hit _ ih => exact .visit (aligned _) hit ih
  exact Prefix.prefix_correct sys input mem admitted before matched

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Proofs
