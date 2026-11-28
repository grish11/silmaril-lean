module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Defs

/-! Shared interned operand IDs for the existing right-materialized diamond. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned

open Pure.SubZero (word)
open Pure.RightIdentityPass (wordProducers)
open GVN.WordNumber.Intern (Id IdVal Table entryIds readId)
open RVSDG (Locals Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

abbrev SharedIds (sigs : List (List (Ty Unit))) :=
  Locals IdVal (extend [] sigs)

structure Cuts (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) where
  table : Table
  entry : Tuple IdVal (dataPorts inputs)
  shared : SharedIds sigs
  first : Id
  second : Id

def Cuts.phi (cuts : Cuts inputs sigs) : Slot → Id
  | .first => cuts.first
  | .second => cuts.second

def numberArm (p : Program inputs sigs [word]) (entry : Tuple IdVal (dataPorts inputs))
    (shared : SharedIds sigs) (table : Table) (slot : Slot) : Table × Id :=
  let arm := p.diamond.arms slot
  let result := GVN.WordNumber.Intern.eval entry arm.dataflow table shared
  (result.1, readId entry result.2 (arm.outputs.get .head))

/-- Extend the same table through entry, shared producers, then each actual arm.
Each arm starts with only the typed shared locals available to it. -/
def numberCuts (p : Program inputs sigs [word]) : Cuts inputs sigs :=
  let entry := entryIds inputs
  let shared := GVN.WordNumber.Intern.eval entry.2 p.diamond.shared entry.1 PUnit.unit
  let first := numberArm p entry.2 shared.2 shared.1 .first
  let second := numberArm p entry.2 shared.2 first.1 .second
  ⟨second.1, entry.2, shared.2, first.2, second.2⟩

/-- Compare only IDs from the one shared table. -/
def check (p : Program inputs sigs [word]) : EntryAdd p → Bool :=
  let cuts := numberCuts p
  let capture : Id := cuts.entry.get p.residual
  fun rep => match addOperands? rep.key with
    | none => false
    | some ⟨(lhs, rhs), _⟩ =>
      let right := readId cuts.entry cuts.shared rhs
      decide (readId cuts.entry cuts.shared lhs = capture) &&
        decide (right = cuts.phi .first) && decide (right = cuts.phi .second)

def findRepresentative? (p : Program inputs sigs [word]) : Option (EntryAdd p) :=
  (wordProducers p.diamond.shared).find? (check p)

/-- Find an entry add by interned IDs and emit the existing typed rewrite. -/
def discoverAndRewrite? (p : Program inputs sigs [word]) : Option (Program inputs sigs [word, word]) := do
  let value ← rightValue? p.suffix
  let rep ← findRepresentative? p
  pure (emit p rep value.val)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned
