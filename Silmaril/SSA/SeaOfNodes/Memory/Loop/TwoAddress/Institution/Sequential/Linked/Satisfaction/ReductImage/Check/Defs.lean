module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Defs

/-! Executable lifts for typed capture reducts. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory
open RVSDG (Port Tuple)
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q R : EntrySignature} {cells : Nat}

def portsOf : (sort : ValueSort) → (args : List ValueSort) → List (Port args sort)
  | _, [] => []
  | .address, .address :: rest => .head :: (portsOf .address rest).map Port.tail
  | .address, .word :: rest => (portsOf .address rest).map Port.tail
  | .word, .address :: rest => (portsOf .word rest).map Port.tail
  | .word, .word :: rest => .head :: (portsOf .word rest).map Port.tail

def valueDecEq (cells : Nat) : (sort : ValueSort) → DecidableEq (Val cells sort)
  | .address => inferInstanceAs (DecidableEq (Address cells))
  | .word => inferInstanceAs (DecidableEq Word)

/-- Construct an initialized tuple with zeros at all ports. A zero-cell
heap has no in-bounds address with which to fill an address port. -/
def defaultInput? (cells : Nat) : (args : List ValueSort) → Option (Tuple (Val cells) args)
  | [] => some .nil
  | .word :: rest => (defaultInput? cells rest).map (Tuple.cons (F := Val cells) (t := ValueSort.word) (0 : Word))
  | .address :: rest =>
    if bound : 0 < cells then
      (defaultInput? cells rest).map (Tuple.cons (F := Val cells) (t := ValueSort.address) ⟨0, bound⟩)
    else none

def admitsInput (cells : Nat) (args : List ValueSort) : Bool := (defaultInput? cells args).isSome

/-- Check that distinct source ports of the selected sort have distinct images. -/
def checkNoIdentification (h : P ⟶ Q) (sort : ValueSort) : Bool :=
  (portsOf sort P.args).all fun left => (portsOf sort P.args).all fun right =>
    decide (Quads.slot (h.port left) = Quads.slot (h.port right) → Quads.slot left = Quads.slot right)

def FibreConsistent (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Prop :=
  ∀ {sort} (left right : Port P.args sort), h.port left = h.port right → input.get left = input.get right

def checkFibresOf (h : P ⟶ Q) (input : Tuple (Val cells) P.args) (sort : ValueSort) : Bool :=
  letI := valueDecEq cells sort
  (portsOf sort P.args).all fun left => (portsOf sort P.args).all fun right =>
    decide (Quads.slot (h.port left) = Quads.slot (h.port right) → input.get left = input.get right)

def checkFibres (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Bool :=
  checkFibresOf h input .word && checkFibresOf h input .address

/-- Fill each target slot from the first source port in its fibre, using
the supplied default at unused target ports. -/
def fill (h : P ⟶ Q) (input : Tuple (Val cells) P.args) (fallback : Tuple (Val cells) Q.args) :
    Tuple (Val cells) Q.args :=
  Quads.tabulate Q.args fun {sort} target =>
    match (portsOf sort P.args).find? (fun p => Quads.slot (h.port p) == Quads.slot target) with
    | some source => input.get source
    | none => fallback.get target

/-- A successful lift supplies a full target tuple at the same cell count. -/
def liftInput? (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Option (Tuple (Val cells) Q.args) := do
  let fallback ← defaultInput? cells Q.args
  if checkFibres h input then some (fill h input fallback) else none

/-- Lift along the composite, then take the second reduct to recover
an intermediate entry compatible with the chosen target. -/
def liftThrough? (h : P ⟶ Q) (k : Q ⟶ R) (entry : Entry P.args cells) :
    Option (Entry Q.args cells × Entry R.args cells) :=
  (liftInput? (h ≫ k) entry.input).map fun input =>
    let target : Entry R.args cells := ⟨input, entry.heap⟩
    (target.reduct k, target)

/-- Check whether every typed source valuation at this count has a target
lift. At one cell, address ports have just one possible value. -/
def checkCoverage (h : P ⟶ Q) (cells : Nat) : Bool :=
  !(admitsInput cells P.args) ||
    (admitsInput cells Q.args &&
      (checkNoIdentification h .word && (decide (cells < 2) || checkNoIdentification h .address)))

/-- The cases of zero cells and two cells determine all-cell-count coverage. -/
def checkExpansive (h : P ⟶ Q) : Bool := checkCoverage h 0 && checkCoverage h 2

/-- Test collisions under the second map only among intermediate slots
used by the first map, separately for each sort. -/
def checkInjectiveOnImage (h : P ⟶ Q) (k : Q ⟶ R) (sort : ValueSort) : Bool :=
  let used := (portsOf sort P.args).map fun port => h.port port
  used.all fun left => used.all fun right =>
    decide (Quads.slot (k.port left) = Quads.slot (k.port right) → Quads.slot left = Quads.slot right)

/-- The final signature must admit a valuation whenever the source does.
Only sorts with distinct values require injectivity. -/
def checkCompositeCoverage (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) : Bool :=
  let preservesSort := fun sort => checkNoIdentification h sort && checkInjectiveOnImage h k sort
  !(admitsInput cells P.args) ||
    (admitsInput cells R.args && (preservesSort .word && (decide (cells < 2) || preservesSort .address)))

def checkCompositeExpansive (h : P ⟶ Q) (k : Q ⟶ R) : Bool :=
  checkCompositeCoverage h k 0 && checkCompositeCoverage h k 2

/-- A zero-cell target address or two same-sort source ports identified by the map. -/
inductive CoverageFailure (P Q : EntrySignature) where
  | emptyTargetAddress (port : Port Q.args .address)
  | collision (sort : ValueSort) (left right : Port P.args sort)

/-- A concrete typed source valuation and the obstruction to lifting it. -/
structure CoverageDiagnostic (P Q : EntrySignature) (cells : Nat) where
  failure : CoverageFailure P Q
  input : Tuple (Val cells) P.args

def CoverageDiagnostic.Valid (h : P ⟶ Q) (diagnostic : CoverageDiagnostic P Q cells) : Prop :=
  match diagnostic.failure with
  | .emptyTargetAddress _ => cells = 0
  | .collision _ left right =>
    h.port left = h.port right ∧ diagnostic.input.get left ≠ diagnostic.input.get right

/-- Find two distinct source ports with the same image, in source port order. -/
def findCollision? (h : P ⟶ Q) (sort : ValueSort) : Option (Port P.args sort × Port P.args sort) :=
  let ports := portsOf sort P.args
  ports.findSome? fun left =>
    (ports.find? fun right =>
      decide (Quads.slot (h.port left) = Quads.slot (h.port right) ∧ Quads.slot left ≠ Quads.slot right)
    ).map (left, ·)

/-- Diagnose coverage starting with a default source valuation. If the target
admits a tuple, separate a colliding pair with values zero and one. -/
def diagnoseCoverage? (h : P ⟶ Q) (cells : Nat) : Option (CoverageDiagnostic P Q cells) :=
  (defaultInput? cells P.args).bind fun input =>
    if !(admitsInput cells Q.args) then
      (portsOf .address Q.args).head?.map fun port => ⟨.emptyTargetAddress port, input⟩
    else if let some (left, right) := findCollision? h .word then
      some ⟨.collision .word left right, Quads.write right (1 : Word) (Quads.write left (0 : Word) input)⟩
    else if two : 1 < cells then
      (findCollision? h .address).map fun (left, right) =>
        ⟨.collision .address left right,
          Quads.write right (⟨1, two⟩ : Address cells)
            (Quads.write left ⟨0, Nat.lt_trans Nat.zero_lt_one two⟩ input)⟩
    else none

/-- Diagnose the composite on its actual source ports. -/
def diagnoseCompositeCoverage? (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) :
    Option (CoverageDiagnostic P R cells) :=
  diagnoseCoverage? (h ≫ k) cells

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
