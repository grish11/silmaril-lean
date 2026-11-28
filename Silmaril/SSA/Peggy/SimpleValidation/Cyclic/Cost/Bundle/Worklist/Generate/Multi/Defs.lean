module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Defs

/-! # Simultaneous operand choices for supplied representative layouts -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi

open PEG
open EPEG (Classes)
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}

structure Layout (g : Graph P params (result :: rest) n 1) where
  size : Nat
  rep : Fin size → Fin n
  vary : List ((i : Fin size) × Fin (g.node (rep i)).inputs.length)

def Layout.skeleton (layout : Layout g) : Skeleton g :=
  ⟨layout.size, layout.rep, none⟩

abbrev Layout.Port (layout : Layout g) :=
  (i : Fin layout.size) × Fin (g.node (layout.rep i)).inputs.length

abbrev Layout.Binding (layout : Layout g) := layout.Port × Fin layout.size

def Layout.required (layout : Layout g) (port : layout.Port) :
    Ref g.sort (g.node (layout.rep port.1)).inputs[port.2] :=
  (g.node (layout.rep port.1)).arg port.2

/-- A complete simultaneous assignment along the supplied distinct ports. -/
def ValidAssignment (classes : Classes n) (layout : Layout g) (assignment : List layout.Binding) : Prop :=
  layout.vary.Nodup ∧ assignment.map Prod.fst = layout.vary ∧
    ∀ binding ∈ assignment,
      g.sort (layout.rep binding.2) = (g.node (layout.rep binding.1.1)).inputs[binding.1.2] ∧
      classes (layout.rep binding.2) = classes (layout.required binding.1).id

variable [DecidableEq Data]

def targets (classes : Classes n) (layout : Layout g) (port : layout.Port) : List (Fin layout.size) :=
  (List.finRange layout.size).filter fun i =>
    (bindAt classes layout.skeleton (layout.required port) i).isSome

def enumerate (classes : Classes n) (layout : Layout g) :
    List layout.Port → List (List layout.Binding)
  | [] => [[]]
  | port :: ports =>
    let tail := enumerate classes layout ports
    (targets classes layout port).flatMap fun i => tail.map ((port, i) :: ·)

/-- Port lists with repeated positions yield no choices. For distinct
ports this enumerates the complete product in layout and address order. -/
def choices (classes : Classes n) (layout : Layout g) : List (List layout.Binding) :=
  if layout.vary.Nodup then enumerate classes layout layout.vary else []

def addressAt (layout : Layout g) (assignment : List layout.Binding) (i : Fin layout.size)
    (slot : Nat) : Option (Fin layout.size) :=
  assignment.findSome? fun (port, addr) =>
    if i = port.1 ∧ slot = port.2.val then some addr else none

def resolve (classes : Classes n) (layout : Layout g) (assignment : List layout.Binding)
    (i : Fin layout.size) (slot : Nat) (required : Ref g.sort t) :
    Option (Ref (g.sort ∘ layout.rep) t) :=
  match addressAt layout assignment i slot with
  | some addr => bindAt classes layout.skeleton required addr
  | none => bindFirst classes layout.skeleton required

def materialize (classes : Classes n) (layout : Layout g) (assignment : List layout.Binding) :
    Option (Candidate g) :=
  materializeWith classes layout.skeleton (resolve classes layout assignment)

/-- A finite pool without an enumeration cap. Missing ordinary bindings
can still prevent a choice from materializing. -/
def pool (classes : Classes n) (layouts : List (Layout g)) : List (Candidate g) :=
  layouts.flatMap fun layout => (choices classes layout).filterMap (materialize classes layout)

variable {Action : Type w} {fuel : Nat}
variable {source : Output P params (result :: rest) 1}
variable {driver : Extension.Worklist.Driver (Output P params (result :: rest) 1) Action}
variable [∀ ins out, DecidableEq (P ins out)]

def select (receipt : CheckedReplay driver fuel source)
    (cost : Candidate receipt.endpoint.2.graph → Nat)
    (layouts : List (Layout receipt.endpoint.2.graph)) :
    Option (Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) :=
  receipt.select cost (pool receipt.endpoint.2.classes layouts)

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi
