module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Defs

/-! Check a finite family of carried word equalities on the native two-backedge program. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family

open Diamond (ValueSort dataPorts)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)
open TwoBackedges (Keys WordSlot numbering redirect)

structure Equation (regs : List (ValueSort Unit)) where
  representative : WordSlot regs
  member : WordSlot regs

abbrev Equations (regs : List (ValueSort Unit)) := List (Equation regs)

variable {regs : List (ValueSort Unit)}

def Holds (equations : Equations regs) (bank : Bank (regs := regs) model) : Prop :=
  ∀ eq ∈ equations, bank.get eq.representative = bank.get eq.member

/-- Merge the whole current member class into the representative's class.
This also joins overlapping nominations. The initial word keys are arguments. -/
def mergeKeys (keys : Keys regs) (eq : Equation regs) : Keys regs :=
  let representative := keys.get eq.representative
  let member := keys.get eq.member
  Quads.tabulate (dataPorts regs) (fun {t} => match t with
    | .value (.data ()) => fun port =>
      let key := keys.get port
      if key.matches member then representative else key
    | .value .predicate => fun port => keys.get port
    | .control _ => fun port => keys.get port
    | .state impossible => nomatch impossible)

def seed (equations : Equations regs) : Keys regs :=
  equations.foldl mergeKeys (WordNumber.entryKeys regs)

def matchesAll (equations : Equations regs) (keys : Keys regs) : Bool :=
  equations.all fun eq => (keys.get eq.representative).matches (keys.get eq.member)

def entryMatches (p : Program Opcode regs word) (equations : Equations regs) : Bool :=
  matchesAll equations (p.preheader.eval (numbering regs) (WordNumber.entryKeys regs))

def headerKeys (p : Program Opcode regs word) (equations : Equations regs) : Keys regs :=
  p.header.eval (numbering regs) (seed equations)

def feedbackFrom (p : Program Opcode regs word) (equations : Equations regs)
    (keys : Keys regs) (side : Bool) : Bool :=
  matchesAll equations ((p.feedback side).eval (numbering regs) keys)

def feedbackMatches (p : Program Opcode regs word) (equations : Equations regs) (side : Bool) : Bool :=
  feedbackFrom p equations (headerKeys p equations) side

def exitMatches (p : Program Opcode regs word) (equations : Equations regs) (replacement : WordSlot regs) : Bool :=
  let keys := headerKeys p equations
  (keys.get p.result).matches (keys.get replacement)

def check (p : Program Opcode regs word) (equations : Equations regs) (replacement : WordSlot regs) : Bool :=
  let keys := headerKeys p equations
  entryMatches p equations &&
    feedbackFrom p equations keys true &&
    feedbackFrom p equations keys false &&
    (keys.get p.result).matches (keys.get replacement)

theorem check_eq_true_iff {p : Program Opcode regs word} {equations : Equations regs}
    {replacement : WordSlot regs} :
    check p equations replacement = true ↔
      entryMatches p equations = true ∧ feedbackMatches p equations true = true ∧
        feedbackMatches p equations false = true ∧ exitMatches p equations replacement = true := by
  simp only [check, feedbackMatches, exitMatches, Bool.and_eq_true, and_assoc]

/-- Evidence that the same family holds on entry, is inductive on both
feedback occurrences, and justifies replacing the post-header return read. -/
structure Certificate (p : Program Opcode regs word) (equations : Equations regs)
    (replacement : WordSlot regs) : Type where
  entry : entryMatches p equations = true
  feedback (side : Bool) : feedbackMatches p equations side = true
  exit : exitMatches p equations replacement = true

def certify? (p : Program Opcode regs word) (equations : Equations regs) (replacement : WordSlot regs) :
    Option (Certificate p equations replacement) :=
  if accepted : check p equations replacement = true then
    let parts := check_eq_true_iff.mp accepted
    some ⟨parts.1, (fun side => match side with | true => parts.2.1 | false => parts.2.2.1), parts.2.2.2⟩
  else none

def rewrite? (p : Program Opcode regs word) (equations : Equations regs) (replacement : WordSlot regs) :
    Option (Program Opcode regs word) :=
  (certify? p equations replacement).map (fun _ => redirect p replacement)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
