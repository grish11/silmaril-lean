module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.ZeroSample
public import Silmaril.SSA.Peggy.EPEG.Selection.Defs

/-! # Figure 6(b–c): moving multiplication into a sample -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Worked.EvalScale

open PEG
open RVSDG (Tuple)
open EPEG (Selection)
open EPEG.Saturation.Extension (Output Plan Row State Step typedNode matchCount)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {site : Fin n}
variable {factor : P [] .count} {op : P [.count, .count] .count}

/-- The dialect interprets the nullary factor as a defined constant, and
the binary operation succeeds for every defined value in its right port. -/
def Law (m : Interpretation.{u,v,x} P) (factor : P [] .count) (op : P [.count, .count] .count) : Prop :=
  ∃ k, m.run factor .nil = some k ∧ ∀ b : m.Value .count, (m.run op (.cons k (.cons b .nil))).isSome

structure Match (g : Graph P params results n l) (site : Fin n)
    (factor : P [] .count) (op : P [.count, .count] .count) where
  siteCount : g.sort site = .count
  loop : Fin l
  constant : Ref g.sort .count
  sampled : Ref g.sort .count
  stream : Ref g.sort .count
  count : Ref g.sort .count
  outer : Rules.HasNode (⟨site, siteCount⟩ : Ref g.sort .count) (.op op)
    (.cons constant (.cons sampled .nil))
  literal : Rules.HasNode constant (.op factor) .nil
  sample : Rules.HasNode sampled (.eval loop) (.cons stream (.cons count .nil))

namespace Match

def rootRef (found : Match g site factor op) : Ref g.sort .count :=
  ⟨site, found.siteCount⟩

theorem hasTypedNode {t : Ty Data} (r : Ref g.sort t)
    (node : Node P params (Fin l) g.sort t) (eq : typedNode r = node) :
    HEq (g.node r.id) node :=
  (eqRec_heq r.typed _).symm.trans (heq_of_eq eq)

def checkSample (site : Fin n) (sort : g.sort site = .count)
    (factor : P [] .count) (op : P [.count, .count] .count)
    (constant sampled : Ref g.sort .count)
    (outer : Rules.HasNode (⟨site, sort⟩ : Ref g.sort .count) (.op op)
      (.cons constant (.cons sampled .nil)))
    (literal : Rules.HasNode constant (.op factor) .nil) :
    (node : Node P params (Fin l) g.sort .count) → typedNode sampled = node →
      Option (Match g site factor op)
  | ⟨_, .eval loop, .cons stream (.cons count .nil)⟩, eq =>
    some ⟨sort, loop, constant, sampled, stream, count, outer, literal, hasTypedNode sampled _ eq⟩
  | _, _ => none

def checkOuter [DecidableEq (P [] .count)] [DecidableEq (P [.count, .count] .count)]
    (site : Fin n) (sort : g.sort site = .count) (factor : P [] .count)
    (op : P [.count, .count] .count) :
    (node : Node P params (Fin l) g.sort .count) →
      typedNode (⟨site, sort⟩ : Ref g.sort .count) = node → Option (Match g site factor op)
  | ⟨_, .op (ins := [.count, .count]) actual, .cons constant (.cons sampled .nil)⟩, eq => do
    if same : actual = op then
      let literal ← matchCount factor constant (typedNode constant) rfl
      checkSample site sort factor op constant sampled
        (by cases same; exact hasTypedNode ⟨site, sort⟩ _ eq) literal.down (typedNode sampled) rfl
    else none
  | _, _ => none

/-- Check the binary opcode, its left nullary operand, and the right eval node. -/
def atSite [DecidableEq Data] [DecidableEq (P [] .count)] [DecidableEq (P [.count, .count] .count)]
    (g : Graph P params results n l) (site : Fin n) (factor : P [] .count)
    (op : P [.count, .count] .count) : Option (Match g site factor op) :=
  if sort : g.sort site = .count then
    checkOuter site sort factor op (typedNode (⟨site, sort⟩ : Ref g.sort .count)) rfl
  else none

def inside (found : Match g site factor op) : Row g :=
  ⟨_, _, .op op, .cons found.constant (.cons found.stream .nil)⟩

def outside (found : Match g site factor op) : Row found.inside.append :=
  ⟨_, _, .eval found.loop, .cons found.inside.fresh (.cons (found.inside.liftRef found.count) .nil)⟩

def oldResult (found : Match g site factor op) : Ref found.outside.sort .count :=
  found.outside.liftRef (found.inside.liftRef found.rootRef)

def equation (found : Match g site factor op) : EPEG.GuardedEquation found.outside.append :=
  ⟨[], ⟨found.oldResult.id, found.outside.fresh.id,
    found.oldResult.typed.trans found.outside.fresh.typed.symm⟩⟩

variable {s : State P params results n l}

def appendInside (found : Match s.graph site factor op) : Step s :=
  ⟨found.inside, [], 0⟩

def appendOutside (found : Match s.graph site factor op) : Step found.appendInside.apply :=
  ⟨found.outside, [.guarded found.equation], 1⟩

def plan (found : Match s.graph site factor op) : Plan s :=
  .next found.appendInside (.next found.appendOutside .stop)

def saturated (found : Match s.graph site factor op) : State P params results (n + 2) l :=
  found.appendOutside.apply

/-- Redirect every ordered occurrence of the matched root to the generated
eval. The graph keeps its shared row table. -/
def redirect (found : Match g site factor op) {t : Ty Data}
    (r : Ref found.outside.sort t) : Ref found.outside.sort t :=
  if same : r.id = found.oldResult.id then
    ⟨found.outside.fresh.id, found.outside.fresh.typed.trans
      (found.oldResult.typed.symm.trans ((congrArg found.outside.sort same.symm).trans r.typed))⟩
  else r

def extract (found : Match g site factor op) : Graph P params results (n + 2) l :=
  found.outside.append.withRoots (found.outside.append.roots.map fun _ => found.redirect)

def selection (found : Match g site factor op) (rank : DemandRank (n + 2) l) :
    Selection found.outside.append found.extract :=
  ⟨fun i => .ofId found.outside.sort i, rank⟩

def rows (found : Match g site factor op) (rank : DemandRank (n + 2) l) (i : Fin (n + 2)) :
    Selection.Row (found.selection rank) i :=
  let r := found.outside.append.node i
  ⟨r.inputs, r.label, r.args, r.args, HEq.rfl, rfl⟩

variable {s : State P params results n l}

def checkExtraction (found : Match s.graph site factor op) (rank : DemandRank (n + 2) l) : Bool :=
  (found.selection rank).check found.saturated.classes &&
    Selection.checkRows (found.rows rank) found.saturated.classes

end Match
end Silmaril.SSA.Peggy.Worked.EvalScale
