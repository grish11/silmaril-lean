module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Defs

/-! # Discover a parentless loop from ordered PEG roots -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic

open RVSDG (Port Tuple)
open Isotope.LambdaSSA.Acyclic.Positional

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results carried ts : List (Ty Data)} {n : Nat} {t : Ty Data}
variable {g : Graph P params results n 1}

/-- Language-level opcode roles. These choices carry no graph addresses. -/
structure Roles (P : InstructionSet.{u,v} Data) where
  zero : P [] .count
  tick : P [.count] .count
  negate : P [.bool] .bool

structure Roles.Laws (roles : Roles P) (m : Interpretation.{u,v,w} P) : Prop where
  zero : m.run roles.zero .nil = some ⟨0⟩
  tick : ∀ k : Nat, m.run roles.tick (.cons ⟨k⟩ .nil) = some ⟨k + 1⟩
  negate : ∀ b : Bool, m.run roles.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩

structure Slot (g : Graph P params results n 1) (t : Ty Data) where
  theta : Ref g.sort t
  initial : Ref g.sort t
  next : Ref g.sort t

def thetaRows (g : Graph P params results n 1) : List (Sigma (Slot g)) :=
  (List.finRange n).filterMap fun i =>
    match g.node i with
    | ⟨_, .theta _, args⟩ =>
      some ⟨g.sort i, ⟨Ref.ofId g.sort i, args.get .head, args.get (.tail .head)⟩⟩
    | _ => none

def slotTuple : (rows : List (Sigma (Slot g))) → Tuple (Slot g) (rows.map Sigma.fst)
  | [] => .nil
  | row :: rows => .cons row.2 (slotTuple rows)

def rootPass (g : Graph P params results n 1) :
    {t : Ty Data} → Ref g.sort t → Node P params (Fin 1) g.sort t → Option (Ref g.sort .count)
  | _, _, ⟨_, .eval _, args⟩ => some (args.get (.tail .head))
  | .count, root, ⟨_, .pass _, _⟩ => some root
  | _, _, _ => none

def firstPass (g : Graph P params results n 1) :
    {ts : List (Ty Data)} → Tuple (Ref g.sort) ts → Option (Ref g.sort .count)
  | _, .nil => none
  | _, .cons root _ => rootPass g root (nodeAt g root)

def readout (g : Graph P params results n 1) (pass : Ref g.sort .count)
    (theta : Tuple (Ref g.sort) carried) :
    {t : Ty Data} → Ref g.sort t → Node P params (Fin 1) g.sort t → Option (Readout carried t)
  | _, _, ⟨_, .eval _, args⟩ =>
    if (args.get (.tail .head)).id = pass.id then
      (lookup (args.get .head) theta).map fun p => .eval p.val
    else none
  | .count, root, ⟨_, .pass _, _⟩ =>
    if root.id = pass.id then some .pass else none
  | _, _, _ => none

/-- Recover the output vector in root order, using a typed lookup of the
sampled θ. All evals and direct pass roots must name the same pass. -/
def readouts (g : Graph P params results n 1) (pass : Ref g.sort .count)
    (theta : Tuple (Ref g.sort) carried) :
    {ts : List (Ty Data)} → Tuple (Ref g.sort) ts → Option (Tuple (Readout carried) ts)
  | _, .nil => some .nil
  | _, .cons root more => do
    let head ← readout g pass theta root (nodeAt g root)
    return .cons head (← readouts g pass theta more)

def sampleTuple (g : Graph P params results n 1) :
    (rows : List (Fin n)) → Tuple (Ref g.sort) (rows.map g.sort)
  | [] => .nil
  | i :: rest => .cons (Ref.ofId g.sort i) (sampleTuple g rest)

/-- Discover exactly the pass/eval leaves reached by the primitive output
slice. Treat candidates as leaves during discovery; boundary checking
subsequently validates the shared pass and sampled θ of every used leaf. -/
def sampleRows (g : Graph P params results n 1) : Option (List (Fin n)) := do
  let candidates := (List.finRange n).filter fun i =>
    (rootPass g (Ref.ofId g.sort i) (g.node i)).isSome
  -- Use a scalar view only for the scheduler. Its designated root is immaterial.
  let some scalar := candidates.head? | none
  let view := g.withRoots (.cons (Ref.ofId g.sort scalar) .nil)
  let captures := Parameters.infer view
  let scope := appendScope (sampleTuple g candidates) captures.refs
  let some order := scopedOrder view scope g.roots | none
  let used := refNumbers g.roots ++ order.flatMap fun i => refNumbers (g.node i).args
  return candidates.filter fun i => i.val ∈ used

def clockCandidate [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n 1) (roles : Roles P) (rows : Tuple (Slot g) carried)
    (i : Fin carried.length) : Option (Port carried .count) := do
  if sort : carried[i] = .count then
    let p : Port carried .count := sort ▸ portAt carried i
    let row := rows.get p
    letI : ∀ t, DecidableEq (Node P params (Fin 1) g.sort t) := fun _ => nodeEq
    if nodeAt g row.initial = .ofLabel (.op roles.zero) .nil ∧
        nodeAt g row.next = .ofLabel (.op roles.tick) (.cons row.theta .nil) then some p
    else none
  else none

/-- Each round propagates the required phase from consumers' operands.
Sampling needs a strict phase drop, while other edge roles may tie.
The rank gate checks all rows, even dead consumers of an eval. -/
def phaseRounds (g : Graph P params results n 1) : Nat → Vector Nat n
  | 0 => Vector.replicate n 0
  | k + 1 =>
    let prior := phaseRounds g k
    Vector.ofFn fun i =>
      let row := g.node i
      (List.finRange row.inputs.length).foldl (fun level slot =>
        let child := prior.get (row.arg slot).id
        let weight := match row.label.kind slot with | .sample _ => 1 | _ => 0
        max level (child + weight)) (prior.get i)

def localTargets (g : Graph P params results n 1) (phase : Fin n → Nat) (i : Fin n) : List (Fin n) :=
  let row := g.node i
  (List.finRange row.inputs.length).filterMap fun slot =>
    let child := (row.arg slot).id
    let kind := row.label.kind slot
    if phase i = phase child ∧ (RankComponent.counter 0).change i child kind = .equal then
      some child
    else none

/-- Use the shared sink-ranking pass for dependencies that tie on the
phase and iteration counter. Inference proposes a rank for the checker. -/
def inferRank (g : Graph P params results n 1) : DemandRank n 1 :=
  let phases := phaseRounds g n
  let order := Rank.rounds (localTargets g phases.get) n
  [.phase phases.get, .counter 0, .phase fun i => (order.get i).getD 0]

structure Recovered (g : Graph P params results n 1) (roles : Roles P) where
  carried : List (Ty Data)
  certificate : Accepted g carried
  zero : certificate.descriptor.zero = roles.zero
  tick : certificate.descriptor.tick = roles.tick
  negate : certificate.descriptor.negate = roles.negate

/-- Recover a candidate from the root pass and all θ rows. Require a
unique unit-counter candidate. The existing checker validates wiring,
rank, and the primitive schedules before a result can be used. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n 1) (roles : Roles P) : Option (Recovered g roles) := do
  let some leaves := sampleRows g | none
  let samples := sampleTuple g leaves
  let some pass := firstPass g samples | none
  let ⟨_, .pass _, args⟩ := nodeAt g pass | none
  let rows := thetaRows g
  let slots := slotTuple rows
  let [clock] := (List.finRange (rows.map Sigma.fst).length).filterMap
    (clockCandidate g roles slots) | none
  let theta := slots.map fun _ row => row.theta
  let some outputs := readouts g pass theta samples | none
  let descriptor : Descriptor g (rows.map Sigma.fst) :=
    ⟨theta, slots.map (fun _ row => row.initial), slots.map (fun _ row => row.next),
      args.get .head, pass, clock, roles.zero, roles.tick, roles.negate, _, samples, outputs⟩
  let checked ← Closed.check g descriptor (inferRank g)
  return ⟨_, checked.val, congrArg Descriptor.zero checked.property,
    congrArg Descriptor.tick checked.property, congrArg Descriptor.negate checked.property⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic
