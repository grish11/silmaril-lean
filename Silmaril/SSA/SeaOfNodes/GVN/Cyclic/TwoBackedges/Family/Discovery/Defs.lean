module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms
public import Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Defs

/-! Discover and check carried word classes of the native two-feedback program. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery

open Diamond (ValueSort dataPorts)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode)
open Quads.Loop.Tail.TwoBackedges (Program)
open TwoBackedges (WordSlot numbering)
open WordNumber (entryKeys)
open scoped Pure.WordNormalize

def slots (regs : List (ValueSort Unit)) : List (WordSlot regs) :=
  (Builder.argumentPorts word regs).map Activation.inputSlot

abbrev Lane (regs : List (ValueSort Unit)) := Fin (slots regs).length

/-- Materialize each round so a later lookup cannot rerun earlier rounds. -/
structure Classes (regs : List (ValueSort Unit)) where
  labels : Vector (Lane regs) (slots regs).length

variable {regs : List (ValueSort Unit)}

instance : CoeFun (Classes regs) (fun _ => Lane regs → Lane regs) :=
  ⟨fun classes => classes.labels.get⟩

def slot (i : Lane regs) : WordSlot regs := (slots regs).get i

scoped instance keyDecidableEq {args : List (Diamond.Ty Unit)} : DecidableEq (WordNumber.Key args) := fun first second =>
  decidable_of_iff (first.matches second = true)
    ⟨WordNumber.Key.eq_of_matches, fun same => same ▸ WordNumber.Key.matches_self first⟩

/-- The first member in register order names each class, regardless of
the incoming numeric label. Omit reflexive equations. -/
def equations (classes : Classes regs) : Equations regs :=
  let representatives := Vector.ofFn (classesOf classes.labels.get)
  (List.finRange (slots regs).length).filterMap fun i =>
    let representative := representatives.get i
    if representative = i then none else some ⟨slot representative, slot i⟩

def entryKey (p : Program Opcode regs word) : Lane regs → WordNumber.Key (dataPorts regs) :=
  let keys := p.preheader.eval (numbering regs) (entryKeys regs)
  fun i => keys.get (slot i)

/-- Initially keep exactly the equal structural preheader results together. -/
def initial (p : Program Opcode regs word) : Classes regs :=
  let keys := Vector.ofFn (entryKey p)
  ⟨Vector.ofFn (classesOf keys.get)⟩

/-- The first key comes from the true feedback block and the second from
the false block. Each block starts with the same completed header keys. -/
def feedbackTable (p : Program Opcode regs word) (classes : Classes regs) :
    Vector (WordNumber.Key (dataPorts regs) × WordNumber.Key (dataPorts regs)) (slots regs).length :=
  let header := Family.headerKeys p (equations classes)
  let onTrue := (p.feedback true).eval (numbering regs) header
  let onFalse := (p.feedback false).eval (numbering regs) header
  Vector.ofFn fun i => (onTrue.get (slot i), onFalse.get (slot i))

def feedbackKeys (p : Program Opcode regs word) (classes : Classes regs) (i : Lane regs) :
    WordNumber.Key (dataPorts regs) × WordNumber.Key (dataPorts regs) :=
  (feedbackTable p classes).get i

/-- Preserve every existing separation and split on either feedback key. -/
def refine (p : Program Opcode regs word) (classes : Classes regs) :
    Classes regs :=
  let feedback := feedbackTable p classes
  ⟨Vector.ofFn (classesOf (fun i => (classes i, feedback.get i)))⟩

def Stable (p : Program Opcode regs word) (classes : Classes regs) : Prop :=
  ∀ i j, classes i = classes j → feedbackKeys p classes i = feedbackKeys p classes j

def checkStable (p : Program Opcode regs word) (classes : Classes regs) : Bool :=
  let feedback := feedbackTable p classes
  (List.finRange (slots regs).length).all fun i =>
    (List.finRange (slots regs).length).all fun j =>
      !(classes i == classes j) || decide (feedback.get i = feedback.get j)

def run (p : Program Opcode regs word) : Nat → Classes regs → Classes regs
  | 0, classes => classes
  | fuel + 1, classes => if checkStable p classes then classes else run p fuel (refine p classes)

def normalize (p : Program Opcode regs word) : Classes regs :=
  run p (slots regs).length (initial p)

def discover (p : Program Opcode regs word) : Equations regs :=
  equations (normalize p)

/-- Replay the original family checker on the discovered classes. The
caller can use the original result slot to request the invariant alone. -/
def certify? (p : Program Opcode regs word) (replacement : WordSlot regs) :
    Option (Certificate p (discover p) replacement) :=
  Family.certify? p (discover p) replacement

def rewrite? (p : Program Opcode regs word) (replacement : WordSlot regs) : Option (Program Opcode regs word) :=
  Family.rewrite? p (discover p) replacement

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery
