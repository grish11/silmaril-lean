module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs

/-! # Ordered returns from one checked primitive loop -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried (result :: rest) n 1}

/-- Only the root interface changes. The first root anchors the existing
scalar boundary, rank and schedule checker on the very same node table. -/
def scalarView (g : Graph P carried (result :: rest) n 1) : Graph P carried [result] n 1 :=
  g.withRoots (.cons (g.roots.get .head) .nil)

/-- Each output position samples the θ for its own selected carried port,
using the very same pass row as the first result. -/
def RootsMatch (scalar : Region.Certificate (scalarView g))
    (slots : Tuple (Port carried) (result :: rest)) : Prop :=
  ∀ t (p : Port (result :: rest) t),
    nodeAt (scalarView g) (g.roots.get p) =
      .ofLabel (.eval 0) (.cons (scalar.descriptor.theta.get (slots.get p))
        (.cons scalar.descriptor.pass .nil))

structure Certificate (g : Graph P carried (result :: rest) n 1) where
  scalar : Region.Certificate (scalarView g)
  slots : Tuple (Port carried) (result :: rest)
  roots : RootsMatch scalar slots

def readSlots (scalar : Region.Certificate (scalarView g)) :
    {ts : List (Ty Data)} → Tuple (Ref g.sort) ts → Option (Tuple (Port carried) ts)
  | _, .nil => some .nil
  | _, .cons root rest => do
    let ⟨_, .eval _, args⟩ := nodeAt (scalarView g) root | none
    let slot ← lookup (args.get .head) scalar.descriptor.theta
    return .cons slot.val (← readSlots scalar rest)

/-- Infer the ordered projection and independently compare each whole
eval row with its carried θ and the common pass. Repeated ports are valid. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried (result :: rest) n 1) : Option (Certificate g) := do
  let scalar ← Automatic.extract (scalarView g)
  let some slots := readSlots scalar g.roots | none
  letI : Decidable (RootsMatch scalar slots) := allPorts _ _ (fun _ _ => nodeEq _ _)
  if checked : RootsMatch scalar slots then some ⟨scalar, slots, checked⟩ else none

def Certificate.exitSlots (cert : Certificate g) : Tuple (Port (.bool :: carried)) (result :: rest) :=
  cert.slots.map fun _ slot => .tail slot

def Certificate.project (cert : Certificate g) (m : Interpretation.{u,v,w} P)
    (final : Tuple m.Value (.bool :: carried)) : Tuple m.Value (result :: rest) :=
  cert.exitSlots.map fun _ slot => final.get slot

/-- Execute one checked loop, then project the final carried store in
the checked output order, preserving repeated positions. -/
def Certificate.revert (cert : Certificate g) : Stmt P true carried (result :: rest) :=
  .seq cert.scalar.revert.body (.project cert.exitSlots)

def Certificate.runFuel (cert : Certificate g) (m : Interpretation.{u,v,w} P) (fuel : Nat)
    (input : Tuple m.Value carried) : Option (Tuple m.Value (result :: rest)) :=
  ((cert.scalar.guard.lower.runLoopFree m input).bind (cert.scalar.runStore m fuel)).map (cert.project m)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle
