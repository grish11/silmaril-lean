module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms

/-! # Ordered PEG eval bundles over one checked θ boundary -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered

open RVSDG (Port Tuple)
open Simple.Revert.While.Region (Certificate nodeAt nodeEq allPorts)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}

/-- Select a root as a scalar view of the same numbered table. The slot
also witnesses that the carried boundary is nonempty. -/
def scalarView (g : Graph P carried carried n 1) (slot : Port carried result) :
    Graph P carried [result] n 1 :=
  g.withRoots (.cons (g.roots.get slot) .nil)

/-- Every ordered output must be an eval of its own carried slot at the
one pass row checked by the scalar certificate. -/
def RootsMatch (g : Graph P carried carried n 1) (slot : Port carried result)
    (scalar : Certificate (scalarView g slot) allowInvariant) : Prop :=
  ∀ t (p : Port carried t), nodeAt (scalarView g slot) (g.roots.get p) =
    .ofLabel (.eval 0) (.cons (scalar.descriptor.theta.get p) (.cons scalar.descriptor.pass .nil))

structure Bundle (g : Graph P carried carried n 1) (slot : Port carried result)
    (allowInvariant : Bool := false) where
  scalar : Certificate (scalarView g slot) allowInvariant
  roots : RootsMatch g slot scalar

/-- Check an existing bundle against the certified reversion region. Row
equality checks both operand references, including distinct same-sort slots. -/
def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried carried n 1) (slot : Port carried result)
    (scalar : Certificate (scalarView g slot) allowInvariant) : Option (Bundle g slot allowInvariant) :=
  letI : Decidable (RootsMatch g slot scalar) := allPorts carried _ (fun _ _ => nodeEq _ _)
  if roots : RootsMatch g slot scalar then some ⟨scalar, roots⟩ else none

/-- Both views solve the very same demand equations. Changing the root
interface changes neither the forest nor any node, sort or demand. -/
theorem Bundle.demandWellFounded (b : Bundle g slot allowInvariant) : WellFounded g.Demand :=
  b.scalar.demandWellFounded

/-- Selecting the scalar root leaves the guarded valuation unchanged. -/
theorem Bundle.denote_scalarView (b : Bundle g slot allowInvariant) (m : TotalModel P)
    (input : Tuple m.toPEG.Value carried) :
    (scalarView g slot).denote m.toPEG input b.scalar.demandWellFounded =
      g.denote m.toPEG input b.demandWellFounded :=
  rfl

/-- Use the existing numbered θ compiler for the shared loop boundary. -/
abbrev Bundle.compile (b : Bundle g slot allowInvariant) := Region.compile b.scalar

end Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered
