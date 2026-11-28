module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Defs

/-! Checked demand summaries over a typed, ordered link prefix. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered

open NestedTheta.Liveness (Demand)
open Continuation (Stack)
open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (ordinaryPort linkedLambda checkWires)
open Isomorphism.RecursiveCall.Numbered.Prefix (Table Row)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {past : List (Ports (Ty V S))} {fn : Function V S}

abbrev Guard (m : Machine.{u, v, w} Op) (table : MemberSummaries V S) :=
  MemberResolution m (some table)

def prepend (summary : MemberSummary V S) (earlier : MemberSummaries V S) : MemberSummaries V S where
  members := summary.fn :: earlier.members
  captures := Fin.cases summary.captures earlier.captures
  live := Fin.cases summary.live earlier.live
  monotone := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact summary.monotone
    · exact earlier.monotone j

/-- Data agreement for a checked callable at its requested result demand. -/
def InputsAgree (summary : MemberSummary V S) (wanted : Demand) (left right :
    Tuple m.Val (summary.captures ++ summary.fn.args)) : Prop :=
  ∀ {ty} (p : Port (summary.captures ++ summary.fn.args) ty), .arg p.index ∈ summary.live wanted →
    left.get p = right.get p

/-- The call certificate accepts any related saved suffix. A blocked call
can therefore still be compared after supplying a common primitive result
and store to both saved stacks. -/
def CallAgrees (actions : Actions m σ) (summary : MemberSummary V S)
    (fL fR : m.Val summary.fn.port) (capsL capsR : Tuple m.Val summary.captures) : Prop :=
  ∀ (observed wanted : Demand) (depth : Nat) {final : Ports (Ty V S)}
    (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (left right : Stack m summary.fn.results final),
    InputsAgree (m := m) summary wanted (prependContext argsL capsL) (prependContext argsR capsR) →
    (∀ outL outR middle, wanted.Agrees outL outR →
      PrefixMatches actions observed depth ⟨.returned outL left, middle⟩ ⟨.returned outR right, middle⟩) →
    PrefixMatches actions observed depth ⟨.eval (.call fL argsL) left, store⟩ ⟨.eval (.call fR argsR) right, store⟩

/-- One common summary table with separately checked targets in each run. -/
structure Dispatch (actions : Actions m σ) (table : MemberSummaries V S) where
  left : Guard m table
  right : Guard m table
  transport : ∀ i fL fR capsL capsR,
    left i fL capsL → right i fR capsR → CallAgrees actions (table.at i) fL fR capsL capsR

/-- Evidence stored at the exact typed linker position of an admitted value. -/
inductive Known (guard : Guard m table) : Isomorphism.RecursiveCall.Family m where
  | ordinary {ty : Ty V S} (value : m.Val ty) (plain : ordinaryPort ty = true) : Known guard value
  | callable (i : Fin table.members.length) (f : m.Val (table.at i).fn.port)
      (caps : Tuple m.Val (table.at i).captures) (checked : guard i f caps) : Known guard f

/-- #3585's table is indexed by each run's actual linker locals. Its callable
cells witness membership in the same dispatch table used by the analysis. -/
structure CheckedPrefix (actions : Actions m σ) (table : MemberSummaries V S)
    (localsL localsR : Locals m.Val past) where
  dispatch : Dispatch actions table
  left : Table (Known dispatch.left) localsL
  right : Table (Known dispatch.right) localsR

/-- The λ sees only the earlier table and its actual typed capture wires. -/
structure Binding (Op : Dialect.{u, v} (ValueSort V S) S) (earlier : MemberSummaries V S)
    (imports : Ports (Ty V S)) (past : List (Ports (Ty V S))) (fn : Function V S) where
  context : Ports (Ty V S)
  captures : Wires imports past context
  sigs : List (Ports (Ty V S))
  body : Code Op (context ++ fn.args) [] sigs fn.results true (some earlier)

namespace Binding

variable (binding : Binding Op table imports past fn)

/-- Keep the same typed body at another physical capture boundary. -/
def withCaptures {past' : List (Ports (Ty V S))}
    (captures : Wires imports past' binding.context) : Binding Op table imports past' fn :=
  ⟨binding.context, captures, binding.sigs, binding.body⟩

def summary : MemberSummary V S :=
  ⟨fn, binding.context, fun wanted => (binding.body.plan wanted).live, binding.body.plan_mono⟩

def term : LambdaTerm Op imports past fn :=
  ⟨binding.context, binding.captures, binding.sigs, binding.body.term⟩

def value (inputs : Tuple m.Val imports) (locals : Locals m.Val past) : m.Val fn.port :=
  linkedLambda binding.term.toGraph inputs locals

def resolved (guard : Guard m table) (inputs : Tuple m.Val imports) (locals : Locals m.Val past) : Prop :=
  ∀ args, binding.body.ResolvedWith guard (prependContext args (binding.captures.read inputs locals))

/-- The first new slot names the actual λ and its capture tuple. The older
slots keep their earlier dispatch evidence. The indices are independent
of the physical linker positions, which are recorded in the prefix table. -/
def extendGuard (guard : Guard m table) (inputs : Tuple m.Val imports) (locals : Locals m.Val past) :
    Guard m (prepend binding.summary table) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact fun target caps => target = binding.value inputs locals ∧ caps = binding.captures.read inputs locals
  · exact guard j

end Binding
end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered
