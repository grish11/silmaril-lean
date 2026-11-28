module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedRows.Defs

/-! # Recover a flat mixed loop from its numbered θ -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse

open Isotope.LambdaSSA (Region)
open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Threaded)
open PureGamma (Op Choice)
open NestedTheta.ExplicitRuntime.PurePrefix (EntryChecked)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A : τ}

abbrev Graph (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) :=
  NestedTheta.Graph (Op (τ := τ) Φ ε) (Threaded (carried A)) [] [Threaded (carried A)] (Threaded (carried A))

def readBody {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {rows : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (t : NestedTheta.Term (Op (τ := τ) Φ ε) args [] rows outs) : Option (MixedRows.Row τ Φ ε × MixedRows.Row τ Φ ε) := do
  let [first, second] ← MixedRows.readScope t | none
  return (first, second)

def readTheta : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Op (τ := τ) Φ ε) ins outs) →
    {sigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Op (τ := τ) Φ ε) kind.entry [] (sigs j) kind.exit) →
    Option (MixedRows.Row τ Φ ε × MixedRows.Row τ Φ ε)
  | _, _, .theta _, _, children => readBody (children (0 : Fin 1))
  | _, _, _, _, _ => none

def read (g : Graph Φ ε A) : Option (MixedRows.Row τ Φ ε × MixedRows.Row τ Φ ε) :=
  match g.toTerm with
  | .bind node children (.ret _) => readTheta node.kind children

section Decode

variable [DecidableEq τ]

def decodePair (value ordered : MixedRows.Row τ Φ ε) : Option (Loop Φ ε A) := do
  let .ordered (.classifier test) := ordered | none
  let ⟨primitive, bottom⟩ ← MixedRows.value A A value
  let test ← MixedRows.instruction A (Choice A) test.op
  return ⟨primitive, bottom, test⟩

def decode : MixedRows.Row τ Φ ε × MixedRows.Row τ Φ ε → Option (Loop Φ ε A × Bool)
  | (left@(.value ..), right) => (decodePair left right).map fun loop => (loop, true)
  | (left, right@(.value ..)) => (decodePair right left).map fun loop => (loop, false)
  | _ => none

/-- Read just the typed labels and the local row order. A candidate alone
does not certify the positions of the data and token wires. -/
def candidate (g : Graph Φ ε A) : Option (Loop Φ ε A × Bool) :=
  (read g).bind decode

end Decode

/-- A flat loop reconstructed from the input and certified by its entire
numbered emission, including feedback and exit wires. -/
structure Fibre (g : Graph Φ ε A) where
  loop : Loop Φ ε A
  pureFirst : Bool
  wiring : loop.compile pureFirst = g

def Fibre.region {g : Graph Φ ε A} (f : Fibre g) : Region Φ := f.loop.region

theorem Fibre.typing {g : Graph Φ ε A} (f : Fibre g) : Region.HasType [A] f.region [A] := f.loop.typing

def Fibre.checked {g : Graph Φ ε A} (f : Fibre g) :
    EntryChecked (a := carriedData A) (b := carriedData A) g.toTerm :=
  f.wiring ▸ f.loop.compileChecked f.pureFirst

variable [DecidableEq τ] [DecidableEq Φ]

/-- Certification checks every input and result address in the actual root
and body tables, as well as their port and opcode signatures. -/
def certify (g : Graph Φ ε A) (c : Loop Φ ε A × Bool) : Option (Fibre g) :=
  letI := MixedRows.decideGraph (c.1.compile c.2) g
  if same : c.1.compile c.2 = g then some ⟨c.1, c.2, same⟩ else none

/-- Graph-only recovery for either emitted body order. -/
def recover (g : Graph Φ ε A) : Option (Fibre g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse
