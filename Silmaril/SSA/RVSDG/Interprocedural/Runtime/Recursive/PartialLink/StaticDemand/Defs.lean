module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs

/-! # Demand through statically resolved, acyclic linked calls -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness
open Continuation.Partial (Config Site)
open Continuation.Partial.Executable (Actions Observation next?)
open Silmaril.Semantics.Dataflow (GenKill)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {entry results : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {loops : Bool}

/-- A supplied singleton-member signature and demand summary. Live origins
refer to the member's captures followed by its formal arguments. -/
structure MemberSummary (V S : Type u) where
  fn : Function V S
  captures : Ports (Ty V S)
  live : Demand → List Address
  monotone : ∀ {low high : Demand}, (∀ p, low p = true → high p = true) → live low ⊆ live high

/-- The supplied summaries share the typed member order of a φ table. -/
structure MemberSummaries (V S : Type u) where
  members : List (Function V S)
  captures : Fin members.length → Ports (Ty V S)
  live : Fin members.length → Demand → List Address
  monotone : ∀ i {low high : Demand}, (∀ p, low p = true → high p = true) → live i low ⊆ live i high

abbrev MemberSummaries.at (table : MemberSummaries V S) (i : Fin table.members.length) :
    MemberSummary V S :=
  ⟨table.members[i], table.captures i, table.live i, table.monotone i⟩

def MemberSummary.singleton (summary : MemberSummary V S) : MemberSummaries V S :=
  ⟨[summary.fn], fun _ => summary.captures, fun _ => summary.live, fun _ => summary.monotone⟩

instance : Coe (MemberSummary V S) (MemberSummaries V S) := ⟨MemberSummary.singleton⟩

variable {member : Option (MemberSummaries V S)}

/-- Check that a statically chosen dispatch target has exactly the captures
named by the call site's typed witnesses. -/
def MemberResolution (m : Machine.{u, v, w} Op) : Option (MemberSummaries V S) → Type (max u v w)
  | none => PUnit
  | some table => (i : Fin table.members.length) →
    m.Val (table.at i).fn.port → Tuple m.Val (table.at i).captures → Prop

/-- An admission for RVSDG bindings with statically checked calls. A static application
names an entry port holding the callable and witnesses its captured values
with typed wires from the caller's entry. The callee can itself have admitted
calls. Reusing the same callee at different call sites permits different result
demands. The optional member table supplies the statically named recursive targets.
The `loops` index enables θ or recursive dispatch. Its default keeps the
settling interface for code without feedback. -/
inductive Code (Op : Dialect.{u, v} (ValueSort V S) S) :
    Ports (Ty V S) → List (Ports (Ty V S)) → List (Ports (Ty V S)) → Ports (Ty V S) →
    (loops : Bool := false) → (member : Option (MemberSummaries V S) := none) → Type (max u v) where
  | ret {entry results : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      {loops : Bool} {member : Option (MemberSummaries V S)} (wires : Wires entry past results) :
      Code Op entry past [] results loops member
  | primitive {entry results ins outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {loops : Bool} {member : Option (MemberSummaries V S)} (opcode : Op ins outs) (operands : Wires entry past ins)
      (rest : Code Op entry (past ++ [outs]) sigs results loops member) :
      Code Op entry past (outs :: sigs) results loops member
  | apply {entry results context : Ports (Ty V S)} {fn : Function V S}
      {past sigs bodySigs : List (Ports (Ty V S))}
      {loops : Bool} {member : Option (MemberSummaries V S)}
      (target : Port entry fn.port) (captures : Wires entry [] context)
      (body : Code Op (context ++ fn.args) [] bodySigs fn.results loops member)
      (arguments : Wires entry past fn.args)
      (rest : Code Op entry (past ++ [fn.results]) sigs results loops member) :
      Code Op entry past (fn.results :: sigs) results loops member
  | gamma {entry results captures outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {loops : Bool} {member : Option (MemberSummaries V S)}
      (extra : Nat) (armSigs : Fin (extra + 2) → List (Ports (Ty V S)))
      (selector : Origin entry past (.control (extra + 2))) (wires : Wires entry past captures)
      (arms : (i : Fin (extra + 2)) → Code Op captures [] (armSigs i) outs loops member)
      (rest : Code Op entry (past ++ [outs]) sigs results loops member) :
      Code Op entry past (outs :: sigs) results loops member
  | theta {entry results carried : Ports (Ty V S)} {past sigs bodySigs : List (Ports (Ty V S))}
      {member : Option (MemberSummaries V S)} (wires : Wires entry past carried)
      (body : Code Op carried [] bodySigs (Theta.BodyResults carried) true member)
      (rest : Code Op entry (past ++ [carried]) sigs results true member) :
      Code Op entry past (carried :: sigs) results true member
  | callAt {entry results : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {table : MemberSummaries V S} (i : Fin table.members.length)
      (target : Origin entry past (table.at i).fn.port) (captures : Wires entry past (table.at i).captures)
      (arguments : Wires entry past (table.at i).fn.args)
      (rest : Code Op entry (past ++ [(table.at i).fn.results]) sigs results true (some table)) :
      Code Op entry past ((table.at i).fn.results :: sigs) results true (some table)

/-- A call whose target and witnesses come directly from the region entry. -/
abbrev Code.familyCall {table : MemberSummaries V S} (i : Fin table.members.length)
    (target : Port entry (table.at i).fn.port) (captures : Wires entry [] (table.at i).captures)
    (arguments : Wires entry past (table.at i).fn.args)
    (rest : Code Op entry (past ++ [(table.at i).fn.results]) sigs results true (some table)) :
    Code Op entry past ((table.at i).fn.results :: sigs) results true (some table) :=
  .callAt i (.arg target) (captures.map fun _ origin => match origin with
    | .arg p => .arg p
    | .output i _ => i.elim0) arguments rest

/-- The original singleton call uses member zero of the supplied table. -/
abbrev Code.memberCall {summary : MemberSummary V S}
    (target : Port entry summary.fn.port) (captures : Wires entry [] summary.captures)
    (arguments : Wires entry past summary.fn.args)
    (rest : Code Op entry (past ++ [summary.fn.results]) sigs results true (some summary)) :
    Code Op entry past (summary.fn.results :: sigs) results true (some summary) :=
  .familyCall (table := summary.singleton) (0 : Fin 1) target captures arguments rest

/-- Erase the static call witnesses. The result uses the runtime's own
primitive, apply, γ and θ nodes, with their original typed operands. -/
def Code.term : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} → {loops : Bool} →
    {member : Option (MemberSummaries V S)} → Code Op entry past sigs results loops member →
    NestedTheta.Term (Instruction Op) entry past sigs results
  | _, _, _, _, _, _, .ret wires => .ret wires
  | _, _, _, _, _, _, .primitive opcode operands rest =>
    .bind ⟨_, .base (.simple (.primitive opcode)), operands, fun i => i.elim0⟩ (fun i => i.elim0) rest.term
  | _, _, _, _, _, _, .apply (fn := fn) target _ _ arguments rest =>
    .bind ⟨_, .base (.simple (.apply fn)), .cons (.arg target) arguments, fun i => i.elim0⟩
      (fun i => i.elim0) rest.term
  | _, _, _, _, _, _, .gamma extra armSigs selector wires arms rest =>
    .bind ⟨_, .base (.gamma extra), .cons selector wires, armSigs⟩
      (fun i => (arms i).term) rest.term
  | _, _, _, _, _, _, .theta (carried := carried) (bodySigs := bodySigs) wires body rest =>
    .bind ⟨carried, .theta carried, wires, fun _ => bodySigs⟩ (fun _ => body.term) rest.term
  | _, _, _, _, _, _, .callAt (table := table) i target _ arguments rest =>
    .bind ⟨_, .base (.simple (.apply (table.at i).fn)), .cons target arguments, fun i => i.elim0⟩
      (fun i => i.elim0) rest.term

/-- Identify a returned port wired straight from the region's entry. -/
def Code.returnArg : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    {loops : Bool} → {member : Option (MemberSummaries V S)} → Code Op entry past sigs results loops member →
    {ty : Ty V S} → Port results ty → Option (Port entry ty)
  | _, _, _, _, _, _, .ret wires, _, p =>
    match wires.get p with
    | .arg q => some q
    | .output _ _ => none
  | _, _, _, _, _, _, .primitive _ _ rest, _, p => rest.returnArg p
  | _, _, _, _, _, _, .apply _ _ _ _ rest, _, p => rest.returnArg p
  | _, _, _, _, _, _, .gamma _ _ _ _ _ rest, _, p => rest.returnArg p
  | _, _, _, _, _, _, .theta _ _ rest, _, p => rest.returnArg p
  | _, _, _, _, _, _, .callAt _ _ _ _ rest, _, p => rest.returnArg p

/-- Entry origins forwarded by the actual result wires retain their values
even when the region returns after a hypothetical primitive resumption. -/
def Code.Forwards (code : Code Op entry past sigs results loops member)
    (input : Tuple m.Val entry) (output : Tuple m.Val results) : Prop :=
  ∀ {ty} (p : Port results ty) (q : Port entry ty), code.returnArg p = some q → output.get p = input.get q

/-- Static call witnesses may use carried values wired directly to the same
port at feedback. These values remain fixed from the initial activation. -/
def Code.Stable {carried : Ports (Ty V S)}
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    (initial next : Tuple m.Val carried) : Prop :=
  ∀ {ty} (p : Port carried ty), body.returnArg (.tail p) = some p → next.get p = initial.get p

/-- Check known targets in the actual local scope. A γ suffix may rely on
any forwarding fact supplied by the selected arm's actual result wires. -/
def Code.ResolvedAt : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} → {loops : Bool} →
    {member : Option (MemberSummaries V S)} → Code Op entry past sigs results loops member →
    MemberResolution m member → Tuple m.Val entry → Locals m.Val past → Prop
  | _, _, _, _, _, _, .ret _, _, _, _ => True
  | _, _, _, _, _, _, .primitive _ _ rest, guard, input, locals =>
    ∀ out, rest.ResolvedAt guard input (locals.snoc out)
  | _, _, _, _, _, _, .apply target captures body _ rest, guard, input, locals =>
    let captured := captures.read input PUnit.unit
    input.get target = .closure captured body.term.toGraph ∧
      (∀ params, body.ResolvedAt guard (prependContext params captured) PUnit.unit) ∧
      (∀ out, rest.ResolvedAt guard input (locals.snoc out))
  | _, _, _, _, _, _, .gamma _ _ _ wires arms rest, guard, input, locals =>
    (∀ i, (arms i).ResolvedAt guard (wires.read input locals) PUnit.unit) ∧
      (∀ i out, (arms i).Forwards (wires.read input locals) out → rest.ResolvedAt guard input (locals.snoc out))
  | _, _, _, _, _, _, .theta wires body rest, guard, input, locals =>
    (∀ next, body.Stable (wires.read input locals) next → body.ResolvedAt guard next PUnit.unit) ∧
      (∀ out, rest.ResolvedAt guard input (locals.snoc out))
  | _, _, _, _, _, _, .callAt i target captures _ rest, guard, input, locals =>
    guard i ((Wires.read (.cons target .nil) input locals).get .head) (captures.read input locals) ∧
      (∀ out, rest.ResolvedAt guard input (locals.snoc out))

/-- A certificate that does not presume any values for pre-existing locals. -/
abbrev Code.ResolvedWith (code : Code Op entry past sigs results loops member)
    (guard : MemberResolution m member) (input : Tuple m.Val entry) : Prop :=
  ∀ locals, code.ResolvedAt guard input locals

/-- Static resolution for code without an external member. -/
abbrev Code.Resolved (code : Code Op entry past sigs results loops) (input : Tuple m.Val entry) : Prop :=
  code.ResolvedWith PUnit.unit input

def resultDemand (pc : Nat) (next : DemandPlan) : Demand :=
  fun p => next.live.contains (.output pc p)

def applyReads {context params : Ports (Ty V S)}
    (live : List Address) {capturePast : List (Ports (Ty V S))}
    (captures : Wires entry capturePast context) (arguments : Wires entry past params) :
    List Address :=
  selectWires (fun _ p => live.contains (.arg p)) captures ++
    selectWires (fun _ p => live.contains (.arg (context.length + p))) arguments

/-- Backwards transfer on the shared schedule. Every primitive attempt reads
all its operands. Each application passes its result demand to the same
summary function of the statically resolved callee. A γ uses the native
transfer to join the live captures of its arms at the binding's output demand.
A θ closes the body summary under its actual feedback wires. -/
def Code.plan (demand : Demand) : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} → {loops : Bool} →
    {member : Option (MemberSummaries V S)} → Code Op entry past sigs results loops member → DemandPlan
  | _, _, past, _, _, _, .ret wires => (⟨[], []⟩ : DemandPlan).prepend past.length (selectWires demand.observes wires)
  | _, _, past, _, _, _, .primitive _ operands rest => (rest.plan demand).prepend past.length operands.addresses
  | _, _, past, _, _, _, .apply _ captures body arguments rest =>
    let next := rest.plan demand
    let live := (body.plan (resultDemand past.length next)).live
    next.prepend past.length (applyReads live captures arguments)
  | _, _, past, _, _, _, .gamma (outs := outs) extra _ selector wires arms rest =>
    let next := rest.plan demand
    let kind : NestedTheta.Kind (Instruction Op) _ outs := .base (.gamma extra)
    let reads := kind.demandReads past.length next.live (.cons selector wires)
      (fun i requested => ((arms i).plan requested).live)
    next.prepend past.length reads
  | _, _, past, _, _, _, .theta (carried := carried) wires body rest =>
    let next := rest.plan demand
    let kind : NestedTheta.Kind (Instruction Op) carried carried := .theta carried
    next.prepend past.length (kind.demandReads past.length next.live wires
      (fun _ requested => (body.plan requested).live))
  | _, _, past, _, _, _, .callAt (table := table) i _ captures arguments rest =>
    let next := rest.plan demand
    next.prepend past.length (applyReads (table.live i (resultDemand past.length next)) captures arguments)

/-- The carried mask coordinates exit demand, the decision, and all restarts. -/
def Code.feedbackLive {carried : Ports (Ty V S)}
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member) (exit : Demand) :
    Feedback.Mask carried.length :=
  Feedback.close exit (fun requested => (body.plan requested).live)

def Code.liveness (code : Code Op entry [] sigs results loops member) (demand : Demand) : GenKill Nat Address :=
  NestedTheta.Liveness.problem (code.plan demand).reads

/-- Executable entry summary, indexed by demand on returned ports (returned
state ports are always observed). -/
def Code.liveIn (code : Code Op entry [] sigs results loops member) (demand : Demand) : List Address :=
  (code.plan demand).live.eraseDups

def Code.AgreesOnInputs (code : Code Op entry [] sigs results loops member) (demand : Demand)
    (left right : Tuple m.Val entry) : Prop :=
  ∀ {ty} (p : Port entry ty), .arg p.index ∈ code.liveIn demand → left.get p = right.get p

/-- Lockstep under the actual runner transitions. At a block, the checked
continuation can be supplied any common hypothetical primitive result and
store. Its behavior can include another block, with the same guarantee. -/
inductive Matches (actions : Actions m σ) (demand : Demand) :
    Config m σ results → Config m σ results → Prop where
  | returned {left right : Tuple m.Val results} {store : σ} (agree : demand.Agrees left right) :
      Matches actions demand ⟨.returned left .halt, store⟩ ⟨.returned right .halt, store⟩
  | step {left right nextL nextR : Config m σ results}
      (stepL : next? actions left = some nextL) (stepR : next? actions right = some nextR)
      (later : Matches actions demand nextL nextR) : Matches actions demand left right
  | blocked {site : Site m} {left right : Continuation.Stack m site.outs results} {store : σ}
      (undefined : (actions.step site.opcode site.input).run store = none)
      (resume : ∀ value nextStore, Matches actions demand
        ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
      Matches actions demand ⟨.eval site.job left, store⟩ ⟨.eval site.job right, store⟩

/-- Settled observations expose equal returned stores, or the very same
typed attempt and store with behaviorally related saved continuations. -/
inductive EndpointsAgree (actions : Actions m σ) (demand : Demand) :
    Observation m σ results → Observation m σ results → Prop where
  | returned {left right : Tuple m.Val results} {store : σ} (agree : demand.Agrees left right) :
      EndpointsAgree actions demand (.returned left store) (.returned right store)
  | blocked {site : Site m} {left right : Continuation.Stack m site.outs results} {store : σ}
      (resume : ∀ value nextStore, Matches actions demand
        ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
      EndpointsAgree actions demand (.blocked ⟨site, left⟩ store) (.blocked ⟨site, right⟩ store)

/-- A finite observation budget counts machine transitions and hypothetical
resumptions. A cut exposes no observation. -/
inductive PrefixMatches (actions : Actions m σ) (demand : Demand) :
    Nat → Config m σ results → Config m σ results → Prop where
  | cut (left right) : PrefixMatches actions demand 0 left right
  | returned {depth : Nat} {left right : Tuple m.Val results} {store : σ}
      (agree : demand.Agrees left right) :
      PrefixMatches actions demand (depth + 1)
        ⟨.returned left .halt, store⟩ ⟨.returned right .halt, store⟩
  | step {depth : Nat} {left right nextL nextR : Config m σ results}
      (stepL : next? actions left = some nextL) (stepR : next? actions right = some nextR)
      (later : PrefixMatches actions demand depth nextL nextR) :
      PrefixMatches actions demand (depth + 1) left right
  | blocked {depth : Nat} {site : Site m} {left right : Continuation.Stack m site.outs results} {store : σ}
      (undefined : (actions.step site.opcode site.input).run store = none)
      (resume : ∀ value nextStore, PrefixMatches actions demand depth
        ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
      PrefixMatches actions demand (depth + 1) ⟨.eval site.job left, store⟩ ⟨.eval site.job right, store⟩

/-- Agreement of the current runner observations, with an independent
remaining budget for looking through saved stacks. -/
inductive PrefixObservationsAgree (actions : Actions m σ) (demand : Demand) (depth : Nat) :
    Observation m σ results → Observation m σ results → Prop where
  | returned {left right : Tuple m.Val results} {store : σ} (agree : demand.Agrees left right) :
      PrefixObservationsAgree actions demand depth (.returned left store) (.returned right store)
  | blocked {site : Site m} {left right : Continuation.Stack m site.outs results} {store : σ}
      (resume : ∀ value nextStore, PrefixMatches actions demand depth
        ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
      PrefixObservationsAgree actions demand depth (.blocked ⟨site, left⟩ store) (.blocked ⟨site, right⟩ store)
  | suspended (left right : Config m σ results) :
      PrefixObservationsAgree actions demand depth (.suspended left) (.suspended right)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
