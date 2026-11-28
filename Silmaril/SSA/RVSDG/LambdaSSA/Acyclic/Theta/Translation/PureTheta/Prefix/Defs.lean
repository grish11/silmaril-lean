module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.Defs

/-! # Recover a mixed θ prefix and an ordered recursive continuation

The root table begins with the mixed θ and its typed carrier conversion.
The remaining ordered scopes are rebased onto the full carrier tuple and
passed to the public recursive recovery entry point. Certification uses
the same checked splice as emission.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix

open Sequential
open Flat.Serial (WirePorts payloadData)
open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Threaded)
open NestedTheta.ExplicitRuntime.PurePrefix (EntryChecked)
open NestedTheta.ExplicitRuntime.PurePrefix.Splice (graph graphChecked)
open StructuredCFG.WithNestedFeedback.Leaf (bridge)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev InputPorts (A : τ) := Threaded (carried A)

abbrev AdapterRows (A X Z : τ) := [InputPorts A, WirePorts A X Z]

abbrev Graph (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A X Z L E D : τ)
    (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (InputPorts A) []
    (AdapterRows A X Z ++ sigs) (WirePorts L E D)

def adapter (Φ : Type u) [HasTy Φ τ] (A X Z : τ) :=
  bridge (Wires.Effect.enterCarrier (Φ := Φ) (A := A) (E := X) (D := Z))

/-- Extend any checked raw producer with a typed carrier conversion. -/
def enterGraph {raw : NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (InputPorts A) [] sigs (InputPorts A)}
    (head : EntryChecked (a := carriedData A) (b := carriedData A) raw.toTerm) (X Z : τ) :=
  graph head (adapter Φ A X Z).2.collect

def enterGraphChecked {raw : NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (InputPorts A) [] sigs (InputPorts A)}
    (head : EntryChecked (a := carriedData A) (b := carriedData A) raw.toTerm) (X Z : τ) :
    EntryChecked (a := carriedData A) (b := payloadData A X Z) (enterGraph head X Z).toTerm :=
  graphChecked head (adapter Φ A X Z).2.collect

def producer (s : Loop Φ ε A) (pureFirst : Bool) (X Z : τ) :=
  enterGraph (s.compileChecked pureFirst) X Z

def producerChecked (s : Loop Φ ε A) (pureFirst : Bool) (X Z : τ) :
    EntryChecked (a := carriedData A) (b := payloadData A X Z) (producer s pureFirst X Z).toTerm :=
  enterGraphChecked (s.compileChecked pureFirst) X Z

/-- Compile the mixed loop and the existing public structured source into
one numbered table. The carrier conversion preserves the θ's live token. -/
def compile (s : Loop Φ ε A) (pureFirst : Bool)
    (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D sigs) : Graph Φ ε A X Z L E D sigs :=
  MixedContinuation.compile (producerChecked s pureFirst X Z) (.mixed tail)

def linkRecovered (s : Loop Φ ε A) (pureFirst : Bool)
    {tail : Flat.Serial.Graph Φ A X Z L E D sigs} (f : Translation.Fibre .mixed tail) : Graph Φ ε A X Z L E D sigs :=
  MixedContinuation.linkRecovered (producerChecked s pureFirst X Z) f

structure Candidate (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A X Z L E D : τ)
    (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) where
  loop : Loop Φ ε A
  pureFirst : Bool
  tail : Flat.Serial.Graph Φ A X Z L E D sigs
  continuation : Translation.Fibre .mixed tail

def Candidate.emit (c : Candidate Φ ε A X Z L E D sigs) : Graph Φ ε A X Z L E D sigs :=
  linkRecovered c.loop c.pureFirst c.continuation

def Candidate.link (c : Candidate Φ ε A X Z L E D sigs) :
    PureTheta.Link (c.loop.compile c.pureFirst) .mixed c.tail :=
  ⟨⟨c.loop, c.pureFirst, rfl⟩, c.continuation⟩

def readAdapter : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    NestedTheta.Kind (PureGamma.Op (τ := τ) Φ ε) ins outs → Option (τ × τ × τ)
  | _, _, .base (.simple (.ordered op)) =>
    match Flat.Numbered.Recognize.opcodeKey op with
    | .enterCarrier a e d => some (a,e,d)
    | _ => none
  | _, _, _ => none

variable [DecidableEq τ] [DecidableEq Φ]

/-- Recover the two components from the root and child tables. The
suffix gets its own local numbering. Uses of earlier origins outside the
carrier boundary fail during rebase. -/
def candidate (g : Graph Φ ε A X Z L E D sigs) : Option (Candidate Φ ε A X Z L E D sigs) :=
  match g.toTerm with
  | .bind root children (.bind conversion _ rest) => do
    let (loop, pureFirst) ← (PureTheta.Reverse.readTheta root.kind children).bind PureTheta.Reverse.decode
    let indices ← readAdapter conversion.kind
    if indices = (A, X, Z) then
      let term ← NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.orderedSuffix
        (NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.boundary [InputPorts A] (WirePorts A X Z)) rest
      let tail := term.toGraph
      let continuation ← Translation.recover .mixed tail
      return ⟨loop, pureFirst, tail, continuation⟩
    else none

structure Fibre (g : Graph Φ ε A X Z L E D sigs) where
  shape : Candidate Φ ε A X Z L E D sigs
  wiring : shape.emit = g

def Fibre.fragment {g : Graph Φ ε A X Z L E D sigs} (f : Fibre g) : Flat.Fragment Φ A E D :=
  f.shape.link.fragment

def certify (g : Graph Φ ε A X Z L E D sigs) (c : Candidate Φ ε A X Z L E D sigs) : Option (Fibre g) :=
  letI := MixedRows.decideGraph c.emit g
  if same : c.emit = g then some ⟨c, same⟩ else none

/-- Recover one actual flat CFG with a certificate for the whole input
graph. The final comparison checks the local θ and every cross-cut use,
including which token reaches the carrier conversion. -/
def recover (g : Graph Φ ε A X Z L E D sigs) : Option (Fibre g) :=
  candidate g >>= certify g

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix
