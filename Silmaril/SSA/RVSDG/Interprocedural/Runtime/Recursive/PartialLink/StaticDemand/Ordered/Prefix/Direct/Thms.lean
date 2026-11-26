module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Sources

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {scope : Scope m}
variable {fn : Function V S}
variable {inputsL inputsR : Tuple m.Val imports}

theorem widen_read {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) (inputs : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val head) :
    (widen wires).read inputs (locals.snoc value) = wires.read inputs locals :=
  Proofs.widen_read wires inputs locals value

theorem seed_selects (family : StaticDemand.Family Op table imports) (i : Fin table.members.length)
    (inputs : Tuple m.Val imports) (origins : Wires imports [memberPorts table.members] (table.at i).captures)
    (found : phiCaptures family i = some origins) :
    let seeded := Scope.seed family inputs inputs
    selects seeded.guardL i ((seedWires i origins).read inputs seeded.localsL) :=
  Proofs.seed_selects family i inputs origins found

theorem new_selects (binding : Binding Op scope.table imports scope.past fn)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table) :
    selects (binding.extendGuard guard inputs locals) (0 : Fin (scope.table.members.length + 1))
      ((newWires binding).read inputs (locals.snoc (.cons (binding.value inputs locals) .nil))) :=
  Proofs.new_selects binding inputs locals guard

theorem capture_reads {F : Ty V S → Type w} {context params : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} (wires : Wires imports past context)
    (inputs : Tuple F imports) (locals : Locals F past) (args : Tuple F params) :
    Boundary.Reads (captureBoundary wires) inputs locals (prependContext args (wires.read inputs locals)) :=
  Proofs.capture_reads wires inputs locals args

theorem forward_reads {F : Ty V S → Type w} {entry child : Ports (Ty V S)}
    {outer past : List (Ports (Ty V S))} (source : Boundary imports entry outer) (wires : Wires entry past child)
    (inputs : Tuple F imports) (locals : Locals F outer) (values : Tuple F entry)
    (reads : Boundary.Reads source inputs locals values) (childLocals : Locals F past) :
    Boundary.Reads (Boundary.forward source wires) inputs locals (wires.read values childLocals) :=
  Proofs.forward_reads source wires inputs locals values reads childLocals

theorem boundary_call {entry : Ports (Ty V S)} (source : Boundary imports entry scope.past)
    (i : Fin scope.table.members.length)
    (target : Port entry (scope.table.at i).fn.port)
    (witnesses : Wires entry [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : Boundary.project source (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (values : Tuple m.Val entry)
    (reads : Boundary.Reads source inputs locals values) :
    guard i (values.get target) (witnesses.read values PUnit.unit) :=
  Proofs.boundary_call source i target witnesses sources expected found same inputs locals guard resolved values reads

theorem projected_call {context params : Ports (Ty V S)} (captures : Wires imports scope.past context)
    (i : Fin scope.table.members.length)
    (target : Port (context ++ params) (scope.table.at i).fn.port)
    (witnesses : Wires (context ++ params) [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : project captures (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (args : Tuple m.Val params) :
    let entry := prependContext args (captures.read inputs locals)
    guard i (entry.get target) (witnesses.read entry PUnit.unit) :=
  boundary_call (captureBoundary captures) i target witnesses sources expected found same inputs locals guard resolved _
    (capture_reads captures inputs locals args)

@[expose] def Routes.seed (family : StaticDemand.Family Op table imports) (inputsL inputsR : Tuple m.Val imports) :
    Routes inputsL inputsR (Scope.seed family inputsL inputsR) :=
  fun i =>
    match found : phiCaptures family i with
    | none => none
    | some captures =>
      some ⟨seedWires i captures,
        seed_selects family i inputsL captures found, seed_selects family i inputsR captures found⟩

@[expose] def Routes.add (routes : Routes inputsL inputsR scope)
    (binding : Binding Op scope.table imports scope.past fn) :
    Routes inputsL inputsR (scope.add binding inputsL inputsR) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact some ⟨newWires binding,
      new_selects binding inputsL scope.localsL scope.guardL, new_selects binding inputsR scope.localsR scope.guardR⟩
  · exact (routes j).map fun route =>
      ⟨widen route.wires,
        (widen_read route.wires inputsL scope.localsL (.cons (binding.value inputsL scope.localsL) .nil)).symm ▸ route.left,
        (widen_read route.wires inputsR scope.localsR (.cons (binding.value inputsR scope.localsR) .nil)).symm ▸ route.right⟩

@[expose] def Routes.skip (routes : Routes inputsL inputsR scope)
    (definition : LambdaTerm Op imports scope.past fn) :
    Routes inputsL inputsR (scope.skip definition inputsL inputsR) := fun i =>
  (routes i).map fun route =>
    ⟨widen route.wires,
      (widen_read route.wires inputsL scope.localsL
        (.cons (linkedLambda definition.toGraph inputsL scope.localsL) .nil)).symm ▸ route.left,
      (widen_read route.wires inputsR scope.localsR
        (.cons (linkedLambda definition.toGraph inputsR scope.localsR) .nil)).symm ▸ route.right⟩

section Check

variable {context : Ports (Ty V S)} {actions : Actions m σ}

@[expose] def resolved {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (captures : Wires imports scope.past context)
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table))
    (inputsL inputsR : Tuple m.Val imports) : Prop :=
  (∀ args, code.ResolvedWith scope.guardL (prependContext args (captures.read inputsL scope.localsL))) ∧
  (∀ args, code.ResolvedWith scope.guardR (prependContext args (captures.read inputsR scope.localsR)))

/-- Resolution for all activations satisfying the boundary map, separately
for each checked link. Untracked ports may have arbitrary runtime values. -/
@[expose] def resolvedAt {entry outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    {loops : Bool} {member : Option (MemberSummaries V S)} (source : Boundary imports entry scope.past)
    (code : Code Op entry past sigs outs loops member) (known : some scope.table = member)
    (inputsL inputsR : Tuple m.Val imports) : Prop :=
  (∀ values, Boundary.Reads source inputsL scope.localsL values → code.ResolvedWith (known ▸ scope.guardL) values) ∧
  (∀ values, Boundary.Reads source inputsR scope.localsR values → code.ResolvedWith (known ▸ scope.guardR) values)

/-- Collect a certificate for each typed arm at its actual finite index. -/
@[expose] def collectArms : (n : Nat) → {P : Fin n → Prop} →
    ((i : Fin n) → Option (PLift (P i))) → Option (PLift (∀ i, P i))
  | 0, _, _ => some ⟨fun i => i.elim0⟩
  | n + 1, _, check => do
    let head ← check 0
    let tail ← collectArms n (fun i => check i.succ)
    pure ⟨Fin.cases head.down tail.down⟩

@[expose] def resolveSite (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    {entry : Ports (Ty V S)} (source : Boundary imports entry scope.past)
    {called : MemberSummaries V S} (known : some scope.table = some called)
    (i : Fin called.members.length) (target : Port entry (called.at i).fn.port)
    (witnesses : Wires entry [] (called.at i).captures) :
    Option (PLift
      ((∀ values, Boundary.Reads source inputsL scope.localsL values →
          (known ▸ scope.guardL : MemberResolution m (some called)) i (values.get target) (witnesses.read values PUnit.unit)) ∧
       (∀ values, Boundary.Reads source inputsR scope.localsR values →
          (known ▸ scope.guardR : MemberResolution m (some called)) i (values.get target) (witnesses.read values PUnit.unit)))) := by
  obtain rfl := Option.some.inj known
  exact match found : Boundary.project source (.cons (.arg target) witnesses), routes i with
  | some sources, some route =>
    if same : sources.addresses = route.wires.addresses then
      let origin := sources.get .head
      if (checked.state.left.available (entry := inputsL) Known.ordinary origin).isSome &&
          (checked.state.right.available (entry := inputsR) Known.ordinary origin).isSome then
        some ⟨fun values reads => boundary_call source i target witnesses sources route.wires found same
          inputsL scope.localsL scope.guardL route.left values reads,
          fun values reads => boundary_call source i target witnesses sources route.wires found same
            inputsR scope.localsR scope.guardR route.right values reads⟩
      else none
    else none
  | _, _ => none

/-- Check direct calls structurally. At each γ, compose the child boundary
map with the actual argument wires and certify all arms and the suffix.
θ and inline closure descriptions require supplied resolution. -/
@[expose] def synthesizeAt (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope) :
    {entry outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    {loops : Bool} → {member : Option (MemberSummaries V S)} →
    (source : Boundary imports entry scope.past) → (code : Code Op entry past sigs outs loops member) →
    (known : some scope.table = member) → Option (PLift (resolvedAt source code known inputsL inputsR))
  | _, _, _, _, _, _, _, .ret _, _ => some ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | _, _, _, _, _, _, source, .primitive _ _ rest, known => synthesizeAt checked routes source rest known
  | _, _, _, _, _, _, source, .familyCall i target witnesses _ rest, known => do
    let site ← resolveSite checked routes source known i target witnesses
    let later ← synthesizeAt checked routes source rest known
    pure ⟨fun values reads => ⟨site.down.1 values reads, later.down.1 values reads⟩,
      fun values reads => ⟨site.down.2 values reads, later.down.2 values reads⟩⟩
  | _, _, _, _, _, _, source, .gamma extra _ _ wires arms rest, known => do
    let children ← collectArms (extra + 2) (fun i =>
      synthesizeAt checked routes (Boundary.forward source wires) (arms i) known)
    let later ← synthesizeAt checked routes source rest known
    pure ⟨fun values reads => ⟨fun locals i =>
      (children.down i).1 _ (forward_reads source wires inputsL scope.localsL values reads locals), later.down.1 values reads⟩,
      fun values reads => ⟨fun locals i =>
        (children.down i).2 _ (forward_reads source wires inputsR scope.localsR values reads locals), later.down.2 values reads⟩⟩
  | _, _, _, _, _, _, _, _, _ => none
termination_by structural _ _ _ _ _ _ _ code _ => code

@[expose] def synthesize (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    (captures : Wires imports scope.past context) {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table)) :
    Option (PLift (resolved captures code inputsL inputsR)) :=
  (synthesizeAt checked routes (captureBoundary captures) code rfl).map fun certificate =>
    ⟨fun args => certificate.down.1 _ (capture_reads captures inputsL scope.localsL args),
      fun args => certificate.down.2 _ (capture_reads captures inputsR scope.localsR args)⟩

end Check

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct
