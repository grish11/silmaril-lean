module

public import Silmaril.Logic.Egglog.Core.Graph.Thms
public import Silmaril.Logic.Egglog.Core.Examples.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Graph.Examples

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Core.Examples

/-- The two target sorts have independent symbol profiles, even though this
particular model interprets both carriers by Nat. -/
abbrev twoSorts : Signature where
  S := Bool
  Op n _ _ := Constructor n (fun _ => ()) ()
  Rel n _ := Predicate n (fun _ => ())
  Function n _ _ := TableSymbol n (fun _ => ()) ()

def selectSort (s : Bool) : Core.Examples.signature ⟶ twoSorts where
  sorts _ := s
  ops o := o
  rels r := r
  functions t := t

/-- This map identifies the two sorts; injectivity is not required. -/
def collapseSorts : twoSorts ⟶ Core.Examples.signature where
  sorts _ := ()
  ops o := o
  rels r := r
  functions t := t

def twoSortModel : Model twoSorts where
  carrier _ := Nat
  op o := match o with | .number v => fun _ => v
  rel r := match r with | .reachable => fun args => args 0 = 1
  row f := match f with | .next => fun args result => args 0 = 0 ∧ result = 1
  functional f := by
    cases f
    intro args x y hx hy
    exact hx.2.trans hy.2.symm

def lookupQuery : Sentence Core.Examples.signature :=
  .query ⟨0, context 0, [lookup (number 0) (number 1)]⟩

/-- A nonidentity symbol map: each numeral constructor becomes its successor. -/
def shiftNumerals : Core.Examples.signature ⟶ Core.Examples.signature where
  sorts := id
  ops o := match o with | .number v => .number (v+1)
  rels r := r
  functions t := t

def functionalFormula : FOL.Formula (signature Core.Examples.signature) (context 3) :=
  .not (.and
    (.and (atom (lookup (.var 0) (.var 1))) (atom (lookup (.var 0) (.var 2))))
    (.not (.eq (.var 1) (.var 2))))

def functionalSentence : FOL.Sentence (signature Core.Examples.signature) :=
  EQtoFOL.closeAll (context 3) functionalFormula

/-- This ordinary FOL structure has every graph row, including two different
outputs for the same input. It cannot be an egglog equality-table model. -/
def nonfunctionalModel : FOL.Structure (signature Core.Examples.signature) where
  carrier _ := Nat
  op o := match o with | .number v => fun _ => v
  rel _ _ := True

end Silmaril.Logic.Egglog.Core.Graph.Examples
