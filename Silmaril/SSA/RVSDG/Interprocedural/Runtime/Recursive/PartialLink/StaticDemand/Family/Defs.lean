module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs

/-! Checked supplied demand summaries for a finite typed φ family. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions Observation)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}

/-- The exact output port selected by a static member number. -/
def memberPort : (members : List (Function V S)) → (i : Fin members.length) →
    Port (memberPorts members) members[i].port
  | [], i => i.elim0
  | f :: rest, i => Fin.cases (motive := fun j => Port (memberPorts (f :: rest)) (f :: rest)[j].port)
    .head (fun j => .tail (memberPort rest j)) i

/-- The λ context starts with the family's recursion references, then that
member's own captures. Supply the actual λ wires and check each summary
against its body's shared transfer. The reference prefix is reserved for
checked static targets. `calls` indexes the body's available summaries.
`past` indexes the actual outer capture wires. -/
structure Family (Op : Dialect.{u, v} (ValueSort V S) S)
    (table : MemberSummaries V S) (imports : Ports (Ty V S))
    (calls : MemberSummaries V S := table) (past : List (Ports (Ty V S)) := []) where
  context : Ports (Ty V S)
  captures : Wires imports past context
  memberWires : (i : Fin table.members.length) →
    Wires (context ++ memberPorts table.members) (memberOutputs (table.members.take i.val))
      (memberPorts table.members ++ (table.at i).captures)
  sigs : Fin table.members.length → List (Ports (Ty V S))
  body : (i : Fin table.members.length) →
    Code Op ((memberPorts table.members ++ (table.at i).captures) ++ (table.at i).fn.args)
      [] (sigs i) (table.at i).fn.results true (some calls)
  closed : ∀ i demand,
    (∀ p, p < (memberPorts table.members).length → .arg p ∉ ((body i).plan demand).live) ∧
    ∀ p, .arg ((memberPorts table.members).length + p) ∈ ((body i).plan demand).live →
      .arg p ∈ table.live i demand

namespace Family

variable {calls : MemberSummaries V S} {past : List (Ports (Ty V S))} (family : Family Op table imports calls past)

def group : PhiTerm Op imports past table.members :=
  ⟨family.context, family.captures, Definitions.ofTable _ fun i =>
    ⟨memberPorts table.members ++ (table.at i).captures,
      family.memberWires i, family.sigs i, (family.body i).term⟩⟩

def memberValue (captured : Tuple m.Val family.context) (i : Fin table.members.length) :
    m.Val (table.at i).fn.port :=
  .member (members := table.members) captured family.group.toGraph.definitions i

def references (captured : Tuple m.Val family.context) : Tuple m.Val (memberPorts table.members) :=
  memberValues table.members (family.memberValue captured)

/-- Read the actual member's λ captures using the same φ arguments and earlier
member outputs as the resolver. -/
def readMember (captured : Tuple m.Val family.context) (i : Fin table.members.length) :
    Tuple m.Val (memberPorts table.members ++ (table.at i).captures) :=
  (family.memberWires i).read (prependContext (family.references captured) captured)
    (memberPrefix table.members i.val (family.memberValue captured))

def dropPrefix {Ty : Type u} {F : Ty → Type w} :
    (front : Ports Ty) → {tail : Ports Ty} → Tuple F (front ++ tail) → Tuple F tail
  | [], _, values => values
  | _ :: rest, _, .cons _ values => dropPrefix rest values

/-- The ordinary capture ports that accompany the member references. -/
def capturedAt (captured : Tuple m.Val family.context) (i : Fin table.members.length) :
    Tuple m.Val (table.at i).captures :=
  dropPrefix (memberPorts table.members) (family.readMember captured i)

def entry (captured : Tuple m.Val family.context) (i : Fin table.members.length)
    (args : Tuple m.Val (table.at i).fn.args) :
    Tuple m.Val ((memberPorts table.members ++ (table.at i).captures) ++ (table.at i).fn.args) :=
  prependContext args (family.readMember captured i)

def guard (captured : Tuple m.Val family.context) : MemberResolution m (some table) :=
  fun i target witnesses => target = family.memberValue captured i ∧ witnesses = family.capturedAt captured i

/-- Check the forwarded reference prefix and each static call against the
actual linked member values and captures. Formal arguments can change at
each dispatch. -/
def ReadyWith (captured : Tuple m.Val family.context) (resolved : MemberResolution m (some calls)) : Prop :=
  ∀ i, family.readMember captured i = prependContext (family.capturedAt captured i) (family.references captured) ∧
    ∀ args, (family.body i).ResolvedWith resolved (family.entry captured i args)

/-- Readiness for a seed with calls confined to its own family. -/
def Ready (family : Family Op table imports) (captured : Tuple m.Val family.context) : Prop :=
  family.ReadyWith captured (family.guard captured)

variable (family : Family Op table imports calls)

/-- Link the whole group and export one statically designated member. -/
def graph (i : Fin table.members.length) : Omega Op imports [(table.at i).fn.port] [memberPorts table.members] :=
  OmegaTerm.toGraph ⟨.bind (.phi family.group)
    (.ret (.cons (.output (0 : Fin 1) (memberPort table.members i)) .nil))⟩

/-- Agreement is on the selected member's actually wired captures and
formal arguments at the positions in its supplied summary. -/
def AgreesOnInputs (i : Fin table.members.length) (demand : Demand) (importedL importedR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val (table.at i).fn.args) : Prop :=
  let left := prependContext argsL (family.capturedAt (family.captures.read importedL PUnit.unit) i)
  let right := prependContext argsR (family.capturedAt (family.captures.read importedR PUnit.unit) i)
  ∀ {ty} (p : Port ((table.at i).captures ++ (table.at i).fn.args) ty), .arg p.index ∈ table.live i demand →
    left.get p = right.get p

def invocation (i : Fin table.members.length) (imported : Tuple m.Val imports)
    (args : Tuple m.Val (table.at i).fn.args) : Job m (table.at i).fn.results :=
  .call (family.memberValue (family.captures.read imported PUnit.unit) i) args

def run (i : Fin table.members.length) (actions : Actions m σ) (fuel unitId : Nat) (imported : Tuple m.Val imports)
    (args : Tuple m.Val (table.at i).fn.args) (store : σ) :
    Except (Failure m σ) (Observation m σ (table.at i).fn.results) :=
  Executable.run actions fuel unitId (family.graph i) imported .head args store

end Family

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
