module

public import Silmaril.SSA.Peggy.Worked.EvalScale.Defs

/-! # Figure 6(c–d): strength reduction of a scaled counter -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Worked.StrengthReduction

open PEG
open EPEG.Saturation.Extension (Row typedNode matchCount)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {site : Fin n}

/-- Instruction identities for the Figure 6 recurrence. The old unary
update represents addition of one in the worked interpretation. -/
structure Profile (P : InstructionSet.{u,v} Data) where
  base : P [] .count
  factor : P [] .count
  step : P [.count] .count
  scale : P [.count, .count] .count
  add : P [.count, .count] .count

variable {ops : Profile P}

/-- Constant folding at the initializer and distributivity at the
feedback. The feedback law compares partial computations, including bottom. -/
structure Law (m : Interpretation.{u,v,x} P) (ops : Profile P) where
  baseValue : m.Value .count
  factorValue : m.Value .count
  definedBase : m.run ops.base .nil = some baseValue
  definedFactor : m.run ops.factor .nil = some factorValue
  fixedBase : m.run ops.scale (.cons factorValue (.cons baseValue .nil)) = some baseValue
  feedback : ∀ a : m.Value .count,
    (m.run ops.step (.cons a .nil)).bind (fun next =>
      m.run ops.scale (.cons factorValue (.cons next .nil))) =
    (m.run ops.scale (.cons factorValue (.cons a .nil))).bind (fun scaled =>
      m.run ops.add (.cons factorValue (.cons scaled .nil)))

structure Match (g : Graph P params results n l) (site : Fin n) (ops : Profile P) where
  siteCount : g.sort site = .count
  loop : Fin l
  constant : Ref g.sort .count
  counter : Ref g.sort .count
  initial : Ref g.sort .count
  update : Ref g.sort .count
  scaleNode : Rules.HasNode (⟨site, siteCount⟩ : Ref g.sort .count) (.op ops.scale)
    (.cons constant (.cons counter .nil))
  factorNode : Rules.HasNode constant (.op ops.factor) .nil
  thetaNode : Rules.HasNode counter (.theta loop) (.cons initial (.cons update .nil))
  baseNode : Rules.HasNode initial (.op ops.base) .nil
  stepNode : Rules.HasNode update (.op ops.step) (.cons counter .nil)

namespace Match

theorem ref_eq_of_id {t : Ty Data} {a b : Ref g.sort t} (same : a.id = b.id) : a = b := by
  cases a; cases b; cases same; rfl

variable [DecidableEq (P [] .count)] [DecidableEq (P [.count] .count)]
variable [DecidableEq (P [.count, .count] .count)]

def checkStep (ops : Profile P) (counter update : Ref g.sort .count) :
    (node : Node P params (Fin l) g.sort .count) → typedNode update = node →
      Option (PLift (Rules.HasNode update (.op ops.step) (.cons counter .nil)))
  | ⟨_, .op (ins := [.count]) instr, .cons input .nil⟩, eq =>
    if hit : instr = ops.step ∧ input.id = counter.id then
      some ⟨by
        have same := ref_eq_of_id hit.2
        rw [← hit.1, ← same]
        exact EvalScale.Match.hasTypedNode update _ eq⟩
    else none
  | _, _ => none

def checkTheta (ops : Profile P) (site : Fin n) (sort : g.sort site = .count)
    (constant counter : Ref g.sort .count)
    (scaleNode : Rules.HasNode (⟨site, sort⟩ : Ref g.sort .count) (.op ops.scale)
      (.cons constant (.cons counter .nil)))
    (factorNode : Rules.HasNode constant (.op ops.factor) .nil) :
    (node : Node P params (Fin l) g.sort .count) → typedNode counter = node →
      Option (Match g site ops)
  | ⟨_, .theta loop, .cons initial (.cons update .nil)⟩, eq => do
    let base ← matchCount ops.base initial (typedNode initial) rfl
    let step ← checkStep ops counter update (typedNode update) rfl
    return ⟨sort, loop, constant, counter, initial, update, scaleNode, factorNode,
      EvalScale.Match.hasTypedNode counter _ eq, base.down, step.down⟩
  | _, _ => none

def checkScale (ops : Profile P) (site : Fin n) (sort : g.sort site = .count) :
    (node : Node P params (Fin l) g.sort .count) → typedNode (⟨site, sort⟩ : Ref g.sort .count) = node →
      Option (Match g site ops)
  | ⟨_, .op (ins := [.count, .count]) instr, .cons constant (.cons counter .nil)⟩, eq => do
    if same : instr = ops.scale then
      let factor ← matchCount ops.factor constant (typedNode constant) rfl
      checkTheta ops site sort constant counter (by
        rw [← same]
        exact EvalScale.Match.hasTypedNode ⟨site, sort⟩ _ eq) factor.down (typedNode counter) rfl
    else none
  | _, _ => none

/-- Match the exact backward edge, not just an update with the right opcode. -/
def atSite [DecidableEq Data] (g : Graph P params results n l) (site : Fin n) (ops : Profile P) :
    Option (Match g site ops) :=
  if sort : g.sort site = .count then
    checkScale ops site sort (typedNode (⟨site, sort⟩ : Ref g.sort .count)) rfl
  else none

end Match

namespace Match

def scaled (found : Match g site ops) : Ref g.sort .count := ⟨site, found.siteCount⟩

/-- The added row consumes the old scale address. Replacing that address
with a theta below creates an actual two-row feedback cycle. -/
def added (found : Match g site ops) : Row g :=
  ⟨_, _, .op ops.add, .cons found.constant (.cons found.scaled .nil)⟩

def resultRef (found : Match g site ops) : Ref found.added.sort .count :=
  found.added.liftRef found.scaled

def thetaArgs (found : Match g site ops) : SSA.RVSDG.Tuple (Ref found.added.sort) [.count, .count] :=
  .cons (found.added.liftRef found.initial) (.cons found.added.fresh .nil)

/-- Replace exactly the matched scale row. The old counter and all its
users remain available, including the pass predicate. -/
def candidate (found : Match g site ops) : Graph P params results (n + 1) l where
  forest := g.forest
  sort := found.added.sort
  node i :=
    if same : found.resultRef.id = i then
      let sortEq := (congrArg found.added.sort same.symm).trans found.resultRef.typed
      sortEq.symm ▸ Node.ofLabel (.theta found.loop) found.thetaArgs
    else found.added.append.node i
  roots := found.added.append.roots

end Match
end Silmaril.SSA.Peggy.Worked.StrengthReduction
