module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Defs

/-! # Partial observations of explicit runtime wires -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial

open OrderedRuntime.Structured
open OrderedState.Partial (Path)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

abbrev Model (P E : Dialect.{u,v} V PUnit.{u + 1}) (σ : Type (max u w)) :=
  OrderedState.Partial.Model.{u,v,w} P E σ

variable (m : Model.{u,v,w} P E σ)

/-- The unchanged port layout has unit runtime slots in the pure scope.
Partial actions consume the ambient store and produce a new store only on success. -/
def erasedModel : OrderedState.Partial.Model.{u,max u v,w} (ThreadedOp P) (ThreadedOp E) σ where
  value := m.value
  runPure
    | @ThreadedOp.op _ _ ins _ op, input =>
      withRuntime PUnit.unit (m.runPure op (splitRuntime ins input).1)
  effect
    | @ThreadedOp.op _ _ ins _ op, input => StateT.mk fun store =>
      Part.map (fun result => (withRuntime PUnit.unit result.1, result.2))
        ((m.effect op (splitRuntime ins input).1).run store)

abbrev Observation := OrderedState.Partial.Abnormal (ThreadedOp E) m.value σ

/-- The attempt is read from the actual operands of the failed wire node.
Retain its exact token separately and keep the ordered positions of the data. -/
def attempt (path : Path) (vertex : Nat) (op : E ins outs)
    (input : Tuple (RuntimeValues m.value σ) (Threaded ins)) :
    OrderedState.Partial.Block (ThreadedOp E) m.value σ :=
  ⟨path, vertex, Threaded ins, Threaded outs, .op op, (boundaryResult input).1, (boundaryResult input).2⟩

def kindAbnormal (path : Path) (vertex : Nat) :
    {ins outs : Ports (Ty V)} → (kind : Kind (Opcode P E) ins outs) →
    (Fin kind.arity → Tuple (wireModel m).Val kind.entry → Tuple (wireModel m).Val kind.exit → Prop) →
    (Fin kind.arity → Tuple (wireModel m).Val kind.entry → Observation m → Prop) →
    Tuple (wireModel m).Val ins → Observation m → Prop
  | _, _, .base (.simple (.ordered _ _ (.pure _))), _, _, _, _ => False
  | _, _, .base (.simple (.ordered i o (.effect op))), _, _, input, obs =>
    ¬ ((wireModel m).primitive (.ordered i o (.effect op)) input).Dom ∧
      obs = .blocked (attempt m path vertex op input)
  | _, _, .base (.gamma _), _, children, .cons tag input, obs =>
    children tag.down input obs
  | _, _, .theta _, body, children, input, obs =>
    OrderedState.Partial.loopAbnormal (erasedModel m)
      (fun x y => body (0 : Fin 1) x (NestedTheta.Partial.tagged (wireModel m) true y))
      (children (0 : Fin 1)) input obs

/-- Follow the numbered term's actual wire reads. A prefix must return a
complete tuple, including its token, before its continuation resumes. -/
def abnormalAt (path : Path) :
    {args outs : Ports (Ty V)} → {past sigs : List (Ports (Ty V))} →
    Term (Opcode P E) args past sigs outs → Tuple (wireModel m).Val args →
    Locals (wireModel m).Val past → Observation m → Prop
  | _, _, _, _, .ret _, _, _, _ => False
  | _, _, past, _, .bind node children rest, input, locals, obs =>
    kindAbnormal m path past.length node.kind
      (fun j x y => NestedTheta.Partial.exec (wireModel m) (children j) x PUnit.unit y)
      (fun j x => abnormalAt (path ++ [(past.length, j.val)]) (children j) x PUnit.unit)
      (node.inputs.read input locals) obs ∨
    ∃ realized, NestedTheta.Partial.kindExec (wireModel m) node.kind
        (fun j x y => NestedTheta.Partial.exec (wireModel m) (children j) x PUnit.unit y)
        (node.inputs.read input locals) realized ∧
      abnormalAt path rest input (locals.snoc realized) obs

def abnormal (g : Graph (Opcode P E) args [] sigs outs)
    (input : Tuple (wireModel m).Val args) (obs : Observation m) : Prop :=
  abnormalAt m [] g.toTerm input PUnit.unit obs

/-- The erased numbered graph runs at the store read from the original
input token wire. Its result keeps the unit slots and the exact final store. -/
noncomputable def observeErased {a : Data args} {b : Data outs}
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    (checked : EntryChecked (a := a) (b := b) g.toTerm)
    (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    Part (OrderedState.Configuration m.value σ (Threaded outs)) :=
  OrderedState.Partial.observe (erasedModel m) checked.erase.toGraph (boundaryResult input).1
    (boundaryResult input).2

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial
