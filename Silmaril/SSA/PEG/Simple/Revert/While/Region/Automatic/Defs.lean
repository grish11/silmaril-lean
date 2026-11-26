module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs

/-! # Automatic admission of a parentless single-loop PEG

The designated root identifies eval, pass and the unary exit opcode.
Each ordered parameter port must initialize exactly one θ in the table.
The scheduler admits primitive guard and feedback slices over that vector.
Row numbers are unrestricted. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic

open RVSDG (Port Tuple)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars results : List (Ty Data)} {result t : Ty Data} {n : Nat}

structure CarriedRow (g : Graph P carried [result] n 1) (t : Ty Data) where
  theta : Ref g.sort t
  initial : Ref g.sort t
  next : Ref g.sort t

/-- Read a θ row candidate for the given typed parameter port. Port
identity distinguishes slots even when their types agree. -/
def candidate [DecidableEq Data] (g : Graph P carried [result] n 1)
    (slot : Port carried t) (i : Fin n) : Option (CarriedRow g t) := do
  let some ref := Ref.check g.sort t i.val | none
  let ⟨_, .theta _, args⟩ := nodeAt g ref | none
  let initial := args.get .head
  let ⟨_, .param p, _⟩ := nodeAt g initial | none
  letI := Check.portEq p slot
  if p = slot then some ⟨ref, initial, args.get (.tail .head)⟩ else none

def candidates [DecidableEq Data] (g : Graph P carried [result] n 1)
    (slot : Port carried t) : List (CarriedRow g t) :=
  (List.finRange n).filterMap (candidate g slot)

def readCarried [DecidableEq Data] (g : Graph P carried [result] n 1) :
    {vars : List (Ty Data)} → Tuple (Port carried) vars → Option (Tuple (CarriedRow g) vars)
  | _, .nil => some .nil
  | _, .cons p ps => do
    let [row] := candidates g p | none
    return .cons row (← readCarried g ps)

def thetaCount (g : Graph P carried [result] n 1) : Nat :=
  (List.finRange n).countP (fun i => (g.node i).label.thetaLoop.isSome)

/-- Read an untrusted boundary from the designated eval and its pass.
The exit opcode must have profile `[bool] → bool`. Its negation law is
a semantic premise of preservation. -/
def inferBoundary [DecidableEq Data] (g : Graph P carried [result] n 1) :
    Option (Descriptor g) := do
  let ⟨_, .eval _, evalArgs⟩ := nodeAt g (g.roots.get .head) | none
  let ⟨_, .theta _, thetaArgs⟩ := nodeAt g (evalArgs.get .head) | none
  let ⟨_, .param returnSlot, _⟩ := nodeAt g (thetaArgs.get .head) | none
  let pass := evalArgs.get (.tail .head)
  let ⟨_, .pass _, passArgs⟩ := nodeAt g pass | none
  let negated := passArgs.get .head
  let ⟨[.bool], .op negate, negArgs⟩ := nodeAt g negated | none
  if thetaCount g != carried.length then none else
    let some rows := readCarried g (ports carried) | none
    return ⟨rows.map (fun _ row => row.theta), rows.map (fun _ row => row.initial),
      rows.map (fun _ row => row.next), negArgs.get .head, negated, negate, pass, returnSlot⟩

def labelPhase : {ins : List (Ty Data)} → {out : Ty Data} →
    Label P carried (Fin 1) ins out → Nat
  | _, _, .eval _ => 2
  | _, _, .pass _ => 1
  | _, _, _ => 0

/-- A separate phase for each sampling boundary lets eval and pass read
arbitrary iteration counts inside the region. -/
def phase (g : Graph P carried results n 1) (i : Fin n) : Nat :=
  labelPhase (g.node i).label

/-- Edges that require a local decrease after comparing phase and loop
counter. The final PEG checker also checks edges on which phase increases
or a sampling edge does not leave its phase. -/
def localTargets (g : Graph P carried results n 1) (i : Fin n) : List (Fin n) :=
  let row := g.node i
  (List.finRange row.inputs.length).filterMap fun slot =>
    let child := (row.arg slot).id
    let kind := row.label.kind slot
    if (RankComponent.phase (phase g)).change i child kind = .equal ∧
        (RankComponent.counter 0).change i child kind = .equal then some child
    else none

/-- Synthesize the local phase component by removing sinks in the
same-phase, same-index dependency graph. The PEG checker validates the
assembled rank against all rows. -/
def inferDemandRank (g : Graph P carried results n 1) : DemandRank n 1 :=
  let ranks := Rank.rounds (localTargets g) n
  [.phase (phase g), .counter 0, .phase fun i => (ranks.get i).getD 0]

/-- Infer the boundary, rank and scheduling orders from the graph's
designated root. The existing region checker is the acceptance gate. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) : Option (Certificate g) := do
  let d ← inferBoundary g
  checkScheduled g d (inferDemandRank g)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic
