module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Defs
public import Silmaril.SSA.PEG.Rules.Defs

/-! # Section 5.3 zero sampling through θ -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension

open PEG
open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l}

/-- Exact table evidence for `eval ℓ (θℓ (initial, feedback), zero)`.
The interpretation of the designated nullary primitive is a separate contract. -/
structure ZeroSample (g : Graph P params results n l) (site : Fin n) (zero : P [] .count) where
  loop : Fin l
  theta : Ref g.sort (g.sort site)
  initial : Ref g.sort (g.sort site)
  feedback : Ref g.sort (g.sort site)
  count : Ref g.sort .count
  evalNode : Rules.HasNode (Ref.ofId g.sort site) (.eval loop) (.cons theta (.cons count .nil))
  thetaNode : Rules.HasNode theta (.theta loop) (.cons initial (.cons feedback .nil))
  countNode : Rules.HasNode count (.op zero) .nil

def typedNode {t : Ty Data} (r : Ref g.sort t) : Node P params (Fin l) g.sort t :=
  r.typed ▸ g.node r.id

private theorem typedNode_has {t : Ty Data} (r : Ref g.sort t)
    (a : Node P params (Fin l) g.sort t) (eq : typedNode r = a) : HEq (g.node r.id) a := by
  rw [← eq]
  exact (eqRec_heq r.typed _).symm

variable [DecidableEq (P [] .count)]

def matchCount (zero : P [] .count) (count : Ref g.sort .count) :
    (node : Node P params (Fin l) g.sort .count) → typedNode count = node →
      Option (PLift (Rules.HasNode count (.op zero) .nil))
  | ⟨_, .op (ins := []) instr, .nil⟩, eq =>
    if same : instr = zero then
      some ⟨by cases same; exact typedNode_has count _ eq⟩
    else none
  | _, _ => none

def matchTheta (site : Fin n) (zero : P [] .count) (loop : Fin l)
    (theta : Ref g.sort (g.sort site)) (count : Ref g.sort .count)
    (evalNode : Rules.HasNode (Ref.ofId g.sort site) (.eval loop) (.cons theta (.cons count .nil))) :
    (node : Node P params (Fin l) g.sort (g.sort site)) → typedNode theta = node →
      Option (ZeroSample g site zero)
  | ⟨_, .theta key, .cons initial (.cons feedback .nil)⟩, eq => do
    if same : key = loop then
      let literal ← matchCount zero count (typedNode count) rfl
      some ⟨loop, theta, initial, feedback, count, evalNode,
        by cases same; exact typedNode_has theta _ eq, literal.down⟩
    else none
  | _, _ => none

def matchEval (site : Fin n) (zero : P [] .count) :
    (node : Node P params (Fin l) g.sort (g.sort site)) → g.node site = node →
      Option (ZeroSample g site zero)
  | ⟨_, .eval loop, .cons theta (.cons count .nil)⟩, eq =>
    matchTheta site zero loop theta count (heq_of_eq eq) (typedNode theta) rfl
  | _, _ => none

/-- Check the outer label, same-loop θ and designated zero literal at a supplied site. -/
def ZeroSample.matchAt (site : Fin n) (zero : P [] .count) : Option (ZeroSample g site zero) :=
  matchEval site zero (g.node site) rfl

namespace ZeroSample

variable {s : State P params results n l} {site : Fin n} {zero : P [] .count}

def row (found : ZeroSample g site zero) : Row g :=
  ⟨_, _, .eval found.loop, .cons found.initial (.cons found.count .nil)⟩

def equation (found : ZeroSample g site zero) : GuardedEquation found.row.append :=
  ⟨[], ⟨site.castSucc, Fin.last n, (found.row.sort_old site).trans found.row.sort_fresh.symm⟩⟩

/-- Append the right-hand side, then submit its equality to the finite worklist. -/
def step (found : ZeroSample s.graph site zero) : Step s :=
  ⟨found.row, [.guarded found.equation], 1⟩

end ZeroSample
end Silmaril.SSA.Peggy.EPEG.Saturation.Extension
