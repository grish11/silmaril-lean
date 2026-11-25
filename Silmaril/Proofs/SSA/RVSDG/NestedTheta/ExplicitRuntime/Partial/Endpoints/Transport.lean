module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Proofs

open OrderedRuntime.Structured
open OrderedState.Partial (Path runOpen runNode)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins out outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (m : Model.{u,v,w} P E σ)

private noncomputable def boundary (d : Data outs) :
    Tuple (RuntimeValues m.value σ) (Threaded outs) ≃
      OrderedState.Configuration m.value σ (Threaded outs) :=
  Equiv.ofBijective boundaryResult (boundaryResult_bijective d)

private theorem boundary_append {xs : Tuple (RuntimeValues m.value σ) ins} (token : σ) :
    boundaryResult (withRuntime token xs) = (withRuntime PUnit.unit (eraseTuple xs), token) := by
  simp only [boundaryResult, erase_append, get_runtime]

private theorem erase_control {n : Nat} {ts : Ports (Ty V)}
    (tag : RuntimeValues m.value σ (.control n)) (data : Tuple (RuntimeValues m.value σ) ts) :
    eraseTuple (.cons tag data) = .cons tag (eraseTuple data) := rfl

private theorem boundary_decode (x : Tuple (Values m.value) ins × σ) :
    boundaryResult (decode x) = (withRuntime PUnit.unit x.1, x.2) := by
  rw [boundaryResult, erase_decode]
  exact congrArg (Prod.mk _) (get_runtime _ _)

private theorem boundary_encode (d : Data ins) (x : Tuple (RuntimeValues m.value σ) (Threaded ins)) :
    boundaryResult x = (withRuntime PUnit.unit (encode x).1, (encode x).2) :=
  (congrArg boundaryResult (decode_encode d x).symm).trans (boundary_decode m (encode x))

private theorem next_boundary (d : Data out) (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past)
    (x : Tuple (RuntimeValues m.value σ) (Threaded out)) :
    readOrigin (nextRuntime past out) entry (locals.snoc x) = (boundaryResult x).2 := by
  rw [← decode_encode d x, next_decode, boundary_decode]

private theorem primitive_action (op : Instruction P E ins outs)
    (x : Tuple (Values m.value) ins × σ) :
    (((erasedModel m).step (eraseInstruction op) (withRuntime PUnit.unit x.1)).run x.2) =
      Part.map (fun y => (withRuntime PUnit.unit y.1, y.2)) ((m.step op x.1).run x.2) := by
  cases op <;> simp only [eraseInstruction, erasedModel, OrderedRuntime.Structured.Model.step,
    split_append] <;> rfl

private theorem primitive_success (i : Data ins) (o : Data out) (op : Instruction P E ins out)
    (x : Tuple (RuntimeValues m.value σ) (Threaded ins))
    (y : Tuple (RuntimeValues m.value σ) (Threaded out)) :
    y ∈ (wireModel m).primitive (.ordered i o op) x ↔
      boundaryResult y ∈ ((erasedModel m).step (eraseInstruction op) (boundaryResult x).1).run
        (boundaryResult x).2 := by
  rw [primitive_mem_iff, boundary_encode m i x, boundary_encode m o y, primitive_action, Part.mem_map_iff]
  have injective : Function.Injective (fun y : Tuple (Values m.value) out × σ =>
      (withRuntime PUnit.unit y.1, y.2)) := by
    intro a b h
    have data_eq := congrArg (fun p => (splitRuntime out p.1).1) h
    simp only [split_append] at data_eq
    exact Prod.ext data_eq (congrArg (fun (p : OrderedState.Configuration m.value σ (Threaded out)) => p.2) h)
  constructor
  · intro member
    exact ⟨_, member, rfl⟩
  · rintro ⟨result, member, same⟩
    rwa [injective same] at member

private theorem primitive_defined (i : Data ins) (o : Data out) (op : E ins out)
    (x : Tuple (RuntimeValues m.value σ) (Threaded ins)) :
    ((wireModel m).primitive (.ordered i o (.effect op)) x).Dom ↔
      (((erasedModel m).effect (.op op) (boundaryResult x).1).run (boundaryResult x).2).Dom := by
  rw [boundary_encode m i x]
  simp only [wireModel, erasedModel, split_append]
  rfl

private theorem iterate_map {X Y : Type*} (e : X ≃ Y)
    {p : X → Bool → X → Prop} {q : Y → Bool → Y → Prop}
    (step : ∀ x again y, p x again y ↔ q (e x) again (e y))
    (x y : X) : Theta.Iterate p x y ↔ Theta.Iterate q (e x) (e y) := by
  constructor
  · intro execution
    induction execution with
    | stop last => exact .stop ((step _ _ _).mp last)
    | again next _ ih => exact .again ((step _ _ _).mp next) ih
  · have backward {a b : Y} (execution : Theta.Iterate q a b) :
        Theta.Iterate p (e.symm a) (e.symm b) := by
      have one {a b : Y} {again : Bool} (r : q a again b) : p (e.symm a) again (e.symm b) :=
        (step _ _ _).mpr (by simpa only [Equiv.apply_symm_apply] using r)
      induction execution with
      | stop last => exact .stop (one last)
      | again next _ ih => exact .again (one next) ih
    intro execution
    simpa only [Equiv.symm_apply_apply] using backward execution

private theorem reach_map {X Y : Type*} {R : X → X → Prop} {S : Y → Y → Prop}
    (f : X → Y) (step : ∀ a b, R a b → S (f a) (f b))
    {x y : X} (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen S (f x) (f y) := by
  induction h with
  | refl => exact .refl
  | tail _ next ih => exact ih.tail (step _ _ next)

private theorem loop_abnormal_map {X Y : Type (max u w)} (e : X ≃ Y)
    {R : X → X → Prop} {S : Y → Y → Prop} (step : ∀ x y, R x y ↔ S (e x) (e y))
    {child : X → Observation m → Prop} {child' : Y → Observation m → Prop} {obs : Observation m}
    (bad : ∀ x, child x obs ↔ child' (e x) obs) (start : X) :
    OrderedState.Partial.loopAbnormal (erasedModel m) R child start obs ↔
      OrderedState.Partial.loopAbnormal (erasedModel m) S child' (e start) obs := by
  have forth x y h := (step x y).mp h
  have back (a b : Y) (h : S a b) : R (e.symm a) (e.symm b) :=
    (step _ _).mpr (by simpa only [Equiv.apply_symm_apply] using h)
  apply or_congr _ (and_congr_right fun _ => ?_)
  · exact e.exists_congr (fun x => (Iff.intro (reach_map e forth) (fun h => by
      simpa only [Equiv.symm_apply_apply] using reach_map e.symm back h)).and (bad x))
  · exact ⟨InfiniteTrace.map e forth, fun h => by
      simpa only [Equiv.symm_apply_apply] using InfiniteTrace.map e.symm back h⟩

private theorem mem_bind
    (node : Node (ErasedOp P E) args past out) (children : Children (Term (ErasedOp P E)) node)
    (rest : Term (ErasedOp P E) args (past ++ [out]) sigs outs)
    (entry : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) (store : σ)
    (output : OrderedState.Configuration m.value σ outs) :
    output ∈ runOpen (erasedModel m) (.bind node children rest) entry locals store ↔
      ∃ middle ∈ runNode (erasedModel m) node children entry locals store,
        output ∈ runOpen (erasedModel m) rest entry (locals.snoc middle.1) middle.2 := by
  simp only [runOpen, Term.denoteOpenWith, StateT.run_bind, Part.bind_eq_bind, Part.mem_bind_iff, runNode]

private abbrev nodeReturns (node : Node (Opcode P E) args past out)
    (children : Children (Term (Opcode P E)) node)
    (entry : Tuple (RuntimeValues m.value σ) args) (locals : Locals (RuntimeValues m.value σ) past) :=
  NestedTheta.Partial.kindExec (wireModel m) node.kind
    (fun j x y => NestedTheta.Partial.exec (wireModel m) (children j) x PUnit.unit y)
    (node.inputs.read entry locals)

private abbrev nodeAbnormal (node : Node (Opcode P E) args past out)
    (children : Children (Term (Opcode P E)) node)
    (entry : Tuple (RuntimeValues m.value σ) args) (locals : Locals (RuntimeValues m.value σ) past)
    (path : Path) :=
  kindAbnormal m path past.length node.kind
    (fun j x y => NestedTheta.Partial.exec (wireModel m) (children j) x PUnit.unit y)
    (fun j x => abnormalAt m (path ++ [(past.length, j.val)]) (children j) x PUnit.unit)
    (node.inputs.read entry locals)

private abbrev erasedAbnormal (node : Node (ErasedOp P E) args past out)
    (children : Children (Term (ErasedOp P E)) node)
    (entry : Tuple (Values m.value) args) (locals : Locals (Values m.value) past)
    (store : σ) (path : Path) :=
  OrderedState.Partial.kindAbnormal (erasedModel m) path past.length node.kind
    (fun j x => runOpen (erasedModel m) (children j) x.1 PUnit.unit x.2)
    (fun j x => OrderedState.Partial.abnormalAt (erasedModel m) (path ++ [(past.length, j.val)])
      (children j) x.1 PUnit.unit x.2)
    (node.inputs.read entry locals, store)

private def Agrees
    (live : Origin (Threaded args) past runtime)
    (t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs))
    (erased : Term (ErasedOp P E) (Threaded args) past sigs (Threaded outs))
    (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past) : Prop :=
  (∀ output, NestedTheta.Partial.exec (wireModel m) t entry locals output ↔
    boundaryResult output ∈ runOpen (erasedModel m) erased (eraseTuple entry) (eraseLocals past locals)
      (readOrigin live entry locals)) ∧
  ∀ path obs, abnormalAt m path t entry locals obs ↔
    OrderedState.Partial.abnormalAt (erasedModel m) path erased (eraseTuple entry) (eraseLocals past locals)
      (readOrigin live entry locals) obs

private theorem bind_transport {live : Origin (Threaded args) past runtime}
    {node : Node (Opcode P E) (Threaded args) past (Threaded out)}
    {children : Children (Term (Opcode P E)) node}
    {rest : Term (Opcode P E) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)}
    {erasedNode : Node (ErasedOp P E) (Threaded args) past (Threaded out)}
    {erasedChildren : Children (Term (ErasedOp P E)) erasedNode}
    {erasedRest : Term (ErasedOp P E) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)}
    (d : Data out) (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past)
    (first : ∀ x, nodeReturns m node children entry locals x ↔
      boundaryResult x ∈ runNode (erasedModel m) erasedNode erasedChildren (eraseTuple entry)
        (eraseLocals past locals) (readOrigin live entry locals))
    (bad : ∀ path obs, nodeAbnormal m node children entry locals path obs ↔
      erasedAbnormal m erasedNode erasedChildren (eraseTuple entry)
        (eraseLocals past locals) (readOrigin live entry locals) path obs)
    (restAgrees : ∀ x, Agrees m (nextRuntime past out) rest erasedRest entry (locals.snoc x)) :
    Agrees m live (.bind node children rest) (.bind erasedNode erasedChildren erasedRest) entry locals := by
  constructor
  · intro output
    rw [NestedTheta.Partial.exec, mem_bind]
    refine (boundary m d).exists_congr fun x => (first x).and ?_
    change _ ↔ boundaryResult output ∈ runOpen (erasedModel m) erasedRest (eraseTuple entry)
      ((eraseLocals past locals).snoc (eraseTuple x)) (boundaryResult x).2
    rw [← erase_snoc, ← next_boundary m d]
    exact (restAgrees x).1 output
  · intro path obs
    simp only [abnormalAt, OrderedState.Partial.abnormalAt]
    refine or_congr (bad path obs) ((boundary m d).exists_congr fun x => (first x).and ?_)
    change _ ↔ OrderedState.Partial.abnormalAt (erasedModel m) path erasedRest (eraseTuple entry)
      ((eraseLocals past locals).snoc (eraseTuple x)) (boundaryResult x).2 obs
    rw [← erase_snoc, ← next_boundary m d]
    exact (restAgrees x).2 path obs

private theorem agrees {a : Data args} {b : Data outs}
    {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t) :
    ∀ (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
      (locals : Locals (RuntimeValues m.value σ) past),
      Agrees m live t checked.erase entry locals := by
  induction checked with
  | @ret args outs a b past live wires =>
    intro entry locals
    constructor
    · intro output
      simp only [NestedTheta.Partial.exec, Checked.erase, runOpen, Term.denoteOpenWith, StateT.run_pure,
        Part.pure_eq_some, Part.mem_some_iff, erase_read, read_appended, erase_append]
      rw [← boundary_append m]
      exact eq_comm.trans (boundaryResult_bijective b).injective.eq_iff.symm
    · intros
      exact Iff.rfl
  | @primitive args outs ins out a b past sigs live i o op wires rest checked ih =>
    intro entry locals
    simp only [Checked.erase]
    refine bind_transport m o entry locals ?_ ?_ (fun x => ih entry (locals.snoc x))
    · intro x
      simp only [nodeReturns, NestedTheta.Partial.kindExec, runNode, Kind.denoteWith,
        primitiveNode, Node.ofBase, erase_read, read_appended, erase_append]
      simpa only [boundary_append m] using
        primitive_success m i o op (withRuntime (readOrigin live entry locals) (wires.read entry locals)) x
    · intro path obs
      cases op with
      | pure => exact Iff.rfl
      | effect op =>
        simp only [nodeAbnormal, erasedAbnormal, kindAbnormal, OrderedState.Partial.kindAbnormal,
          primitiveNode, Node.ofBase, eraseInstruction, attempt, erase_read, read_appended,
          erase_append, boundary_append m]
        refine and_congr_left' ?_
        simpa only [boundary_append m] using
          not_congr (primitive_defined m i o op (withRuntime (readOrigin live entry locals) (wires.read entry locals)))
  | @gamma args outs ins out a b past sigs extra choice live i o wires childSigs children rest arms checked ihArms ih =>
    intro entry locals
    simp only [Checked.erase]
    refine bind_transport m o entry locals ?_ ?_ (fun x => ih entry (locals.snoc x))
    · intro x
      simp only [nodeReturns, NestedTheta.Partial.kindExec, runNode, Kind.denoteWith, erase_read,
        read_cons, read_appended, erase_control m]
      let tag := (readOrigin choice entry locals).down
      let input := withRuntime (readOrigin live entry locals) (wires.read entry locals)
      have sim := (ihArms tag input PUnit.unit).1 x
      change _ ↔ boundaryResult x ∈ runOpen (erasedModel m) (arms tag).erase
        (eraseTuple input) PUnit.unit (input.get (runtimePort ins)) at sim
      simpa only [runOpen, input, get_runtime] using sim
    · intro path obs
      simp only [nodeAbnormal, erasedAbnormal, kindAbnormal, OrderedState.Partial.kindAbnormal,
        erase_read, read_cons, read_appended, erase_control m]
      let tag := (readOrigin choice entry locals).down
      let input := withRuntime (readOrigin live entry locals) (wires.read entry locals)
      have sim := (ihArms tag input PUnit.unit).2 (path ++ [(past.length, tag.val)]) obs
      change _ ↔ OrderedState.Partial.abnormalAt (erasedModel m) _ (arms tag).erase
        (eraseTuple input) PUnit.unit (input.get (runtimePort ins)) obs at sim
      simpa only [input, get_runtime] using sim
  | @theta args outs ins a b past sigs live i wires bodySigs children rest admitted checked ihBody ih =>
    intro entry locals
    let child := children (0 : Fin 1)
    let erasedChild := (admitted (0 : Fin 1)).erase
    have step (before after : Tuple (RuntimeValues m.value σ) (Threaded ins)) (again : Bool) :
        NestedTheta.Partial.exec (wireModel m) child before PUnit.unit
          (NestedTheta.Partial.tagged (wireModel m) again after) ↔
        OrderedState.tagged again (boundaryResult after) ∈
          runOpen (erasedModel m) erasedChild (boundaryResult before).1 PUnit.unit (boundaryResult before).2 :=
      (ihBody (0 : Fin 1) before PUnit.unit).1 _
    let input := withRuntime (readOrigin live entry locals) (wires.read entry locals)
    simp only [Checked.erase]
    refine bind_transport m i entry locals ?_ ?_ (fun x => ih entry (locals.snoc x))
    · intro x
      simp only [nodeReturns, NestedTheta.Partial.kindExec, runNode, Kind.denoteWith, erase_read, read_appended,
        erase_append]
      have iterations := iterate_map (boundary m i)
        (p := fun before again after => NestedTheta.Partial.exec (wireModel m) child before PUnit.unit
          (NestedTheta.Partial.tagged (wireModel m) again after))
        (q := fun before again after => OrderedState.tagged again after ∈
          runOpen (erasedModel m) erasedChild before.1 PUnit.unit before.2)
        (fun before again after => step before after again) input x
      change _ ↔ Theta.Iterate _ (boundaryResult input) (boundaryResult x) at iterations
      have returns := OrderedState.Partial.mem_theta
        (fun entry => erasedChild.denoteOpenWith (OrderedState.Partial.interpretation (erasedModel m))
          entry PUnit.unit) (boundaryResult input) (boundaryResult x)
      have both := iterations.trans returns.symm
      simp only [input, child, erasedChild, boundary_append m] at both
      exact both
    · intro path obs
      simp only [nodeAbnormal, erasedAbnormal, kindAbnormal, OrderedState.Partial.kindAbnormal,
        erase_read, read_appended, erase_append]
      have bad (before : Tuple (RuntimeValues m.value σ) (Threaded ins)) :
          abnormalAt m (path ++ [(past.length, 0)]) child before PUnit.unit obs ↔
          OrderedState.Partial.abnormalAt (erasedModel m) (path ++ [(past.length, 0)]) erasedChild
            (boundaryResult before).1 PUnit.unit (boundaryResult before).2 obs :=
        (ihBody (0 : Fin 1) before PUnit.unit).2 _ _
      have loops := loop_abnormal_map m (boundary m i)
        (R := fun before after => NestedTheta.Partial.exec (wireModel m) child before PUnit.unit
          (NestedTheta.Partial.tagged (wireModel m) true after))
        (S := OrderedState.Partial.Restart (erasedModel m) fun before =>
          runOpen (erasedModel m) erasedChild before.1 PUnit.unit before.2)
        (child := fun before => abnormalAt m (path ++ [(past.length, 0)]) child before PUnit.unit)
        (child' := fun before => OrderedState.Partial.abnormalAt (erasedModel m) (path ++ [(past.length, 0)])
          erasedChild before.1 PUnit.unit before.2)
        (obs := obs) (fun before after => step before after true) bad input
      simp only [input, child, erasedChild, boundary, Equiv.ofBijective_apply, boundary_append m] at loops
      exact loops

theorem exec_iff {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past)
    (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    NestedTheta.Partial.exec (wireModel m) t entry locals output ↔
      boundaryResult output ∈ runOpen (erasedModel m) checked.erase (eraseTuple entry)
        (eraseLocals past locals) (readOrigin live entry locals) :=
  (agrees m checked entry locals).1 output

theorem abnormalAt_iff {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past) (path : Path) (obs : Observation m) :
    abnormalAt m path t entry locals obs ↔
      OrderedState.Partial.abnormalAt (erasedModel m) path checked.erase (eraseTuple entry)
        (eraseLocals past locals) (readOrigin live entry locals) obs :=
  (agrees m checked entry locals).2 path obs

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Proofs
