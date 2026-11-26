module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs

/-! Typed linker sources used to check direct captured calls. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct

open Isomorphism.Local.Gamma (extendOrigin)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}

def capturePort {Ty : Type u} {params : Ports Ty} {ty : Ty} :
    (context : Ports Ty) → Port (context ++ params) ty → Option (Port context ty)
  | [], _ => none
  | _ :: _, .head => some .head
  | _ :: rest, .tail p => (capturePort rest p).map Port.tail

/-- A region entry port may come from an exact typed linker origin. -/
structure Boundary {Ty : Type u} (imports entry : Ports Ty) (past : List (Ports Ty)) where
  get : {ty : Ty} → Port entry ty → Option (Origin imports past ty)

/-- The enclosing λ's capture wires define the initial boundary map.
Formal parameters have no tracked linker origin. -/
def captureBoundary {Ty : Type u} {imports context params : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires imports past context) : Boundary imports (context ++ params) past :=
  ⟨fun p => (capturePort context p).map fun q => wires.get q⟩

/-- Follow the actual region boundary wires into the enclosing entry. Outputs
of earlier local bindings have no tracked linker origin. -/
def Boundary.forward {Ty : Type u} {imports entry child : Ports Ty} {outer past : List (Ports Ty)}
    (source : Boundary imports entry outer) (wires : Wires entry past child) : Boundary imports child outer :=
  ⟨fun p => match wires.get p with
    | .arg q => source.get q
    | .output _ _ => none⟩

/-- Keep only origins that the θ body returns from the same carried port.
Computed results and permutations have no provenance at the next entry. -/
def Boundary.feedback {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member) : Boundary imports carried outer :=
  ⟨fun p => match body.returnArg (.tail p) with
    | some q => if q.index = p.index then source.get p else none
    | none => none⟩

/-- Project the requested operands through the boundary map. Untracked
ports elsewhere on the boundary do not prevent projection. -/
def Boundary.project {Ty : Type u} {imports entry : Ports Ty} {outer past : List (Ports Ty)}
    (source : Boundary imports entry outer) : {users : Ports Ty} →
    Wires entry past users → Option (Wires imports outer users)
  | _, .nil => some .nil
  | _, .cons (.arg p) rest => do
    let origin ← source.get p
    let tail ← Boundary.project source rest
    pure (.cons origin tail)
  | _, .cons (.output _ _) _ => none

/-- Compose capture edges with the actual linker wires. -/
def project {Ty : Type u} {imports context params users : Ports Ty} {past localSigs : List (Ports Ty)}
    (wires : Wires imports past context) (requested : Wires (context ++ params) localSigs users) :
    Option (Wires imports past users) := Boundary.project (captureBoundary wires) requested

/-- Every tracked port agrees with the value read at its linker origin. -/
def Boundary.Reads {Ty : Type u} {F : Ty → Type w} {imports entry : Ports Ty} {outer : List (Ports Ty)}
    (source : Boundary imports entry outer) (inputs : Tuple F imports) (locals : Locals F outer)
    (values : Tuple F entry) : Prop :=
  ∀ {ty} (p : Port entry ty) {origin}, source.get p = some origin →
    values.get p = (Wires.read (.cons origin .nil : Wires imports outer [ty]) inputs locals).get .head

def widen {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) : Wires args (past ++ [head]) users :=
  wires.map fun _ origin => extendOrigin origin head

def phiCaptures (family : StaticDemand.Family Op table imports) (i : Fin table.members.length) :
    Option (Wires imports [memberPorts table.members] (table.at i).captures) :=
  project (widen family.captures) (StaticDemand.Family.dropPrefix (memberPorts table.members) (family.memberWires i))

/-- The target and its capture witnesses, taken together in call order. -/
abbrev CallPorts (table : MemberSummaries V S) (i : Fin table.members.length) :=
  (table.at i).fn.port :: (table.at i).captures

def seedWires (i : Fin table.members.length)
    (captures : Wires imports [memberPorts table.members] (table.at i).captures) :
    Wires imports [memberPorts table.members] (CallPorts table i) :=
  .cons (.output (0 : Fin 1) (memberPort table.members i)) captures

def newWires {scope : Scope m} {fn : Function V S} (binding : Binding Op scope.table imports scope.past fn) :
    Wires imports (scope.past ++ [[fn.port]])
      (CallPorts (prepend binding.summary scope.table) (0 : Fin (scope.table.members.length + 1))) :=
  .cons ((lastExport scope.past fn : Wires imports _ [fn.port]).get .head) (widen binding.captures)

def selects (guard : Guard m table) (i : Fin table.members.length)
    (values : Tuple m.Val (CallPorts table i)) : Prop :=
  guard i (values.get .head) (StaticDemand.Family.dropPrefix [(table.at i).fn.port] values)

/-- Source wires for one checked slot, with resolution evidence for their
actual values on both sides of the linker. -/
structure Route (inputsL inputsR : Tuple m.Val imports) (scope : Scope m)
    (i : Fin scope.table.members.length) where
  wires : Wires imports scope.past (CallPorts scope.table i)
  left : selects scope.guardL i (wires.read inputsL scope.localsL)
  right : selects scope.guardR i (wires.read inputsR scope.localsR)

/-- Slots remain usable by explicit resolution even when there is no
direct-source description of their captures. -/
abbrev Routes (inputsL inputsR : Tuple m.Val imports) (scope : Scope m) :=
  (i : Fin scope.table.members.length) → Option (Route inputsL inputsR scope i)

section Tracking

open Continuation.Partial.Executable (Actions)

variable {scope : Scope m} {σ : Type (max u v w)} {actions : Actions m σ}
variable {inputsL inputsR : Tuple m.Val imports}

/-- A call's typed operands project to the supplied slot's exact sources,
and the target origin has checked membership in both links. -/
def TrackedSite (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    {entry : Ports (Ty V S)} (source : Boundary imports entry scope.past)
    (i : Fin scope.table.members.length) (target : Port entry (scope.table.at i).fn.port)
    (witnesses : Wires entry [] (scope.table.at i).captures) : Prop :=
  ∃ sources route,
    Boundary.project source (.cons (.arg target) witnesses) = some sources ∧
    routes i = some route ∧ sources.addresses = route.wires.addresses ∧
    (checked.state.left.available (entry := inputsL) Known.ordinary (sources.get .head)).isSome = true ∧
    (checked.state.right.available (entry := inputsR) Known.ordinary (sources.get .head)).isSome = true

/-- Direct forwarding derivations. A γ requires tracking at every arm
under its composed boundary. A θ tracks only same-port feedback sources in
its body. Both require tracked suffixes under the enclosing boundary. -/
inductive Tracked (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope) :
    {entry outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Boundary imports entry scope.past → Code Op entry past sigs outs true (some scope.table) → Prop where
  | ret {entry outs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      {source : Boundary imports entry scope.past} (wires : Wires entry past outs) :
      Tracked checked routes source (.ret wires)
  | primitive {entry ins results outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {source : Boundary imports entry scope.past} {opcode : Op ins outs} {operands : Wires entry past ins}
      {rest : Code Op entry (past ++ [outs]) sigs results true (some scope.table)} :
      Tracked checked routes source rest → Tracked checked routes source (.primitive opcode operands rest)
  | call {entry outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {source : Boundary imports entry scope.past} {i : Fin scope.table.members.length}
      {target : Port entry (scope.table.at i).fn.port} {witnesses : Wires entry [] (scope.table.at i).captures}
      {args : Wires entry past (scope.table.at i).fn.args}
      {rest : Code Op entry (past ++ [(scope.table.at i).fn.results]) sigs outs true (some scope.table)} :
      TrackedSite checked routes source i target witnesses → Tracked checked routes source rest →
      Tracked checked routes source (.familyCall (table := scope.table) i target witnesses args rest)
  | gamma {entry captures outputs outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {source : Boundary imports entry scope.past} {extra : Nat} {armSigs : Fin (extra + 2) → List (Ports (Ty V S))}
      {selector : Origin entry past (.control (extra + 2))} {wires : Wires entry past captures}
      {arms : (i : Fin (extra + 2)) → Code Op captures [] (armSigs i) outputs true (some scope.table)}
      {rest : Code Op entry (past ++ [outputs]) sigs outs true (some scope.table)} :
      (∀ i, Tracked checked routes (Boundary.forward source wires) (arms i)) → Tracked checked routes source rest →
      Tracked checked routes source (.gamma extra armSigs selector wires arms rest)
  | theta {entry carried outs : Ports (Ty V S)} {past sigs bodySigs : List (Ports (Ty V S))}
      {source : Boundary imports entry scope.past} {wires : Wires entry past carried}
      {body : Code Op carried [] bodySigs (Theta.BodyResults carried) true (some scope.table)}
      {rest : Code Op entry (past ++ [carried]) sigs outs true (some scope.table)} :
      Tracked checked routes ((source.forward wires).feedback body) body → Tracked checked routes source rest →
      Tracked checked routes source (.theta wires body rest)

end Tracking

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct
