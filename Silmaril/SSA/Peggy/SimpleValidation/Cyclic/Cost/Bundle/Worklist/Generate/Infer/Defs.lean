module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Defs

/-! # Layouts from a checked primitive loop update and return slice -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer

open PEG
open PEG.Simple.Revert.While
open PEG.Simple.Revert.While.Region (Schedule)
open PEG.Reindex.Automatic (refIds)
open EPEG.Saturation
open EPEG.Saturation.Extension
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}

/-- Read exactly the primitive binding rows of a checked schedule. -/
def scheduledRows {graph : Graph P params [result] n 1} :
    {outs : List (Ty Data)} → {roots : Tuple (Ref graph.sort) outs} →
    {vars : List (Ty Data)} → {scope : Tuple (Ref graph.sort) vars} →
    Schedule graph false roots scope → List (Fin n)
  | _, _, _, _, .done _ => []
  | _, _, _, _, .bind i _ _ _ _ _ tail => i :: scheduledRows tail

/-- Keep each source address just once in the ordered return, loop
boundary and checked guard/update schedules, in first-occurrence order. -/
def sharedRows (cert : Region.Bundle.Certificate g) : List (Fin n) :=
  let d := cert.scalar.descriptor
  (refIds g.roots ++ [d.pass.id, d.negated.id, d.guard.id] ++
    refIds d.initial ++ refIds d.theta ++ refIds d.next ++
    scheduledRows cert.scalar.guard ++ scheduledRows cert.scalar.update).eraseDups

def shared (g : Graph P params (result :: rest) n 1) (rows : List (Fin n)) : Multi.Layout g :=
  ⟨rows.length, rows.get, []⟩

/-- A typed source operand position, before translating row addresses. -/
abbrev Use (g : Graph P params (result :: rest) n 1) :=
  (row : Fin n) × Fin (g.node row).inputs.length

def uses (g : Graph P params (result :: rest) n 1)
    (body : List (Fin n)) (leaf : Fin n) : List (Use g) :=
  body.flatMap fun row =>
    let node := g.node row
    (List.finRange node.inputs.length).filterMap fun slot =>
      if (node.arg slot).id = leaf then some ⟨row, slot⟩ else none

def nullaryPrimitive (g : Graph P params (result :: rest) n 1) (leaf : Fin n) : Bool :=
  match g.node leaf with
  | ⟨[], .op _, _⟩ => true
  | _ => false

/-- In this fragment one layout appends one copy of a nullary primitive,
and exposes its second update use to the existing wiring enumerator. -/
def copySite (g : Graph P params (result :: rest) n 1) (body : List (Fin n))
    (leaf : Fin n) : Option (Use g) :=
  if nullaryPrimitive g leaf then (uses g body leaf)[1]? else none

/-- Append one representative and translate a source operand position
to the first retained address of its consumer. -/
def duplicateAt (g : Graph P params (result :: rest) n 1)
    (rows : List (Fin n)) (leaf : Fin n) (site : Use g) : Option (Multi.Layout g) :=
  let base := shared g (rows ++ [leaf])
  (List.finRange base.size).findSome? fun i =>
    if same : base.rep i = site.1 then
      some { base with vary := [⟨i, same.symm ▸ site.2⟩] }
    else none

def fromSlice (g : Graph P params (result :: rest) n 1)
    (rows body : List (Fin n)) : List (Multi.Layout g) :=
  shared g rows :: body.filterMap fun leaf =>
    (copySite g body leaf).bind (duplicateAt g rows leaf)

variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- Check the ordered primitive-loop boundary first, then infer layouts
from its actual schedules. Failure of the seed check yields an empty pool. -/
def layouts (g : Graph P params (result :: rest) n 1) : List (Multi.Layout g) :=
  match Region.Bundle.extract (Reindex.Automatic.cacheRows g) with
  | none => []
  | some cert => fromSlice g (sharedRows cert) (scheduledRows cert.scalar.update)

variable {Action : Type w} {fuel : Nat}
variable {source : Output P params (result :: rest) 1}
variable {driver : Extension.Worklist.Driver (Output P params (result :: rest) 1) Action}

def select (receipt : CheckedReplay driver fuel source)
    (cost : Candidate receipt.endpoint.2.graph → Nat) :
    Option (Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes) :=
  Multi.select receipt cost (layouts receipt.endpoint.2.graph)

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer
