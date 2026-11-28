module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Defs
public import Silmaril.SSA.PEG.Reindex.Automatic.Defs
import Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Cache

/-! # Finite ordered candidate pools from representative layouts -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate

open PEG
open EPEG (Classes Selection)
open EPEG.Saturation
open EPEG.Saturation.Extension
open RVSDG (Tuple)
open PEG.Simple.Revert.While.Region.Automatic (inferDemandRank)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}

/-- A row layout and at most one operand position to vary. No candidate
operand addresses or ordered root addresses are part of the skeleton. -/
structure Skeleton (g : Graph P params (result :: rest) n 1) where
  size : Nat
  rep : Fin size → Fin n
  vary : Option ((i : Fin size) × Fin (g.node (rep i)).inputs.length) := none

variable [DecidableEq Data]

/-- A local binding must have the required sort and source class. -/
def bindAt (classes : Classes n) (layout : Skeleton g) (required : Ref g.sort t) (i : Fin layout.size) :
    Option (Ref (g.sort ∘ layout.rep) t) :=
  if classes (layout.rep i) = classes required.id then
    if typed : g.sort (layout.rep i) = t then some ⟨i, typed⟩ else none
  else none

def bindFirst (classes : Classes n) (layout : Skeleton g) (required : Ref g.sort t) :
    Option (Ref (g.sort ∘ layout.rep) t) :=
  (List.finRange layout.size).findSome? (bindAt classes layout required)

/-- Every compatible address for the distinguished port, or just the
default policy when there is no distinguished port. -/
def choices (classes : Classes n) (layout : Skeleton g) : List (Option (Fin layout.size)) :=
  match layout.vary with
  | none => [none]
  | some port =>
    let operand := (g.node (layout.rep port.1)).arg port.2
    ((List.finRange layout.size).filter fun i => (bindAt classes layout operand i).isSome).map some

def bindTuple (layout : Skeleton g)
    (resolve : ∀ {t}, Nat → Ref g.sort t → Option (Ref (g.sort ∘ layout.rep) t)) :
    {ts : List (Ty Data)} → Nat → Tuple (Ref g.sort) ts → Option (Tuple (Ref (g.sort ∘ layout.rep)) ts)
  | _, _, .nil => some .nil
  | _, position, .cons first rest => do
    let some operand := resolve position first | none
    (bindTuple layout resolve (position + 1) rest).map (.cons operand)

def bindOperand (classes : Classes n) (layout : Skeleton g) (choice : Option (Fin layout.size))
    (i : Fin layout.size) (slot : Nat) (required : Ref g.sort t) :
    Option (Ref (g.sort ∘ layout.rep) t) :=
  match layout.vary, choice with
  | some focus, some target =>
    if i = focus.1 ∧ slot = focus.2.val then bindAt classes layout required target
    else bindFirst classes layout required
  | _, _ => bindFirst classes layout required

/-- Resolve the ordered wires and materialize a typed candidate with
common-row evidence. Admission still checks rank, class wiring and
SIMPLE reversion independently. -/
def materializeWith (classes : Classes n) (layout : Skeleton g)
    (resolve : ∀ {t}, Fin layout.size → Nat → Ref g.sort t → Option (Ref (g.sort ∘ layout.rep) t)) :
    Option (Candidate g) := do
  let args (i : Fin layout.size) :=
    bindTuple layout (resolve i) 0 (g.node (layout.rep i)).args
  let some roots := bindTuple layout (fun _ => bindFirst classes layout) 0 g.roots | none
  if wired : (List.finRange layout.size).all (fun i => (args i).isSome) = true then
    let operands i := (args i).get (List.all_eq_true.mp wired i (List.mem_finRange i))
    let graph : Graph P params (result :: rest) layout.size 1 :=
      ⟨g.forest, g.sort ∘ layout.rep, fun i => Node.ofLabel (g.node (layout.rep i)).label (operands i), roots⟩
    let cached := Reindex.Automatic.cacheRows graph
    let selection : Selection g cached :=
      ⟨fun i => Ref.ofId g.sort (layout.rep i), inferDemandRank cached⟩
    some ⟨layout.size, cached, selection, fun i =>
      let row := g.node (layout.rep i)
      ⟨row.inputs, row.label, row.args, operands i, HEq.rfl,
        by exact Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.cached_node graph i⟩⟩
  else none

def materialize (classes : Classes n) (layout : Skeleton g) (choice : Option (Fin layout.size)) :
    Option (Candidate g) :=
  materializeWith classes layout (bindOperand classes layout choice)

/-- Enumerate every materializable point in the supplied finite layout
space. There is no candidate cap. -/
def pool (classes : Classes n) (layouts : List (Skeleton g)) : List (Candidate g) :=
  layouts.flatMap fun layout => (choices classes layout).filterMap (materialize classes layout)

variable {Action : Type w} {fuel : Nat}
variable {source : Output P params (result :: rest) 1}
variable {driver : Extension.Worklist.Driver (Output P params (result :: rest) 1) Action}
variable [∀ ins out, DecidableEq (P ins out)]

def select (receipt : CheckedReplay driver fuel source)
    (cost : Candidate receipt.endpoint.2.graph → Nat)
    (layouts : List (Skeleton receipt.endpoint.2.graph)) :
    Option (Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) :=
  receipt.select cost (pool receipt.endpoint.2.classes layouts)

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate
