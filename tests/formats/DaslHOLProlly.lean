module

import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions.Thms
import Mathlib.Tactic.FinCases
import Batteries.Data.Except
meta import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions.Defs

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Prolly (Read ByteKey)
open Silmaril.Logic.HOLLight
open Silmaril.ProofFormats.DaslSyntax
open Silmaril.Semantics.Naming (graph graph_binding)
open scoped Silmaril.Formats.Dasl.Prolly

namespace DaslHOLProllyTest

def premise : Tm := .fvar 0 .bool

def block (node : Silmaril.Semantics.Prolly.Block Nat ByteKey Unit) : Wire.ReadResult (Shallow Nat) :=
  match HOL.Prolly.assumptionCodec.encode? node with
  | some value => .found value
  | none => .invalidWire

def blocks (available : Bool) : Read Nat
  | 0 => block (.branch 1 [(HOL.hypothesisKey.encode premise, 1)])
  | 1 => if available then block (.leaf [(HOL.hypothesisKey.encode premise, ())]) else .missing
  | 2 => block (.leaf [([], ())])
  | _ => .missing

def offline : Read Nat := fun _ => .missing

theorem missingRoot : HOL.Prolly.readAssumptions offline 1 2 0 = .error (.block (.missing 0)) := rfl

def namedPremise : Named Nat := Encode.list.encode [.string "fvar", .string (Nat.repr 0), .string "bool"]

def namedList : Named Nat := Encode.list.encode [.string "hyps", namedPremise, namedPremise]

def objects : Nat → Option (Shallow Nat)
  | 3 => some (Encode.list.encode [.string "fvar", .string (Nat.repr 0), .string "bool"])
  | 4 => some (Encode.list.encode [.string "hyps", Encode.list.encode [.string "fvar", .string (Nat.repr 0), .string "bool"],
      Encode.list.encode [.string "fvar", .string (Nat.repr 0), .string "bool"]])
  | _ => none

def store : Store Nat := ⟨graph objects, graph fun _ => none⟩

theorem binding : store.Binding := ⟨graph_binding _, graph_binding _⟩

private theorem expandsPremise : Expands store
    (Encode.list.encode [.string "fvar", .string (Nat.repr 0), .string "bool"]) namedPremise := by
  apply Expands.list
  intro index
  change Fin 3 at index
  fin_cases index <;> exact .string _

private theorem writePremise : HOL.tm.write inlineAll premise = namedPremise.erase := by
  apply congrArg (Tree.list 3)
  funext index
  fin_cases index <;> rfl

theorem premiseRoot : HOL.tm.names store 3 premise :=
  ⟨_, ⟨namedPremise, ⟨_, rfl, expandsPremise⟩, rfl⟩, inlineAll, writePremise⟩

theorem listRoot : HOL.assumptions.names store 4 [premise, premise] := by
  have expands : FullNames store 4 namedList := by
    refine ⟨_, rfl, Expands.list ?_⟩
    intro index
    change Fin 3 at index
    fin_cases index
    · exact .string _
    · exact expandsPremise
    · exact expandsPremise
  refine ⟨_, ⟨namedList, expands, rfl⟩, inlineAll, ?_⟩
  change HOL.assumptions.write inlineAll [premise, premise] = namedList.erase
  have forms : HOL.assumptions.codec.encode [premise, premise] =
      .list [.atom "hyps", HOL.tm.codec.encode premise, HOL.tm.codec.encode premise] := by
    change (taggedList "hyps").encode (HOL.tm.codec.listCodec.encode [premise, premise]) = _
    rw [Encode.TotalCodec.listCodec_encode]
    rfl
  rw [Syntax.write, forms]
  apply congrArg (Tree.list 3)
  funext index
  fin_cases index
  · rfl
  · exact writePremise
  · exact writePremise

theorem typing : HasType initialSignature [] premise .bool := .fvar 0 trivial

theorem setDerives (complete : HOL.Prolly.readAssumptions (blocks true) 1 2 0 = .ok [premise]) :
    HOL.Prolly.derives store (blocks true) 1 2 initialSignature (∅ : Theory) 0 3 :=
  (HOL.Prolly.derives_iff_kernel binding complete premiseRoot).mpr (by simpa using Derives.assume (theory := ∅) typing)

theorem sameSet : [premise].toFinset = [premise, premise].toFinset := by simp

theorem listDerives : HOL.derives store initialSignature (∅ : Theory) 4 3 :=
  system_iff.mpr ⟨[premise, premise], premise, listRoot, premiseRoot, by
    simpa using Derives.assume (theory := ∅) typing⟩

theorem entails {model : Model initialSignature}
    (complete : HOL.Prolly.readAssumptions (blocks true) 1 2 0 = .ok [premise]) :
    HOL.Prolly.entails store (blocks true) 1 2 model 0 3 :=
  (HOL.Prolly.entails_iff_list binding listRoot complete sameSet premiseRoot).mp
    (HOL.derives_le_entails (by simp [Models]) 4 3 listDerives)

theorem unavailableNotRefuted (complete : HOL.Prolly.readAssumptions (blocks true) 1 2 0 = .ok [premise]) :
    (¬ ∃ hyps, HOL.Prolly.assumptions offline 1 2 0 hyps) ∧
      HOL.Prolly.derives store (blocks true) 1 2 initialSignature (∅ : Theory) 0 3 :=
  ⟨HOL.Prolly.no_assumptions_of_error missingRoot,
    (HOL.Prolly.derives_iff_list binding listRoot complete sameSet premiseRoot).mp listDerives⟩

end DaslHOLProllyTest

open DaslHOLProllyTest (blocks premise)

private def check (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

public def main : IO Unit := do
  check (decide (HOL.Prolly.readAssumptions (blocks true) 1 2 0 = .ok [premise])) "read linked assumptions"
  check (decide (HOL.Prolly.readAssumptions (blocks false) 1 2 0 = .error (.block (.missing 1)))) "missing child"
  check (decide (HOL.Prolly.readAssumptions (blocks true) 1 1 0 = .error (.block (.fuel 1)))) "insufficient fuel"
  check (decide (HOL.Prolly.readAssumptions (blocks true) 1 2 2 = .error (.invalidKey []))) "invalid term key"

#print axioms HOL.Prolly.assumptions_binding
#print axioms HOL.Prolly.assumptions_iff_read
#print axioms HOL.Prolly.assumptions_sound
#print axioms HOL.Prolly.no_assumptions_of_error
#print axioms HOL.Prolly.derives_iff_kernel
#print axioms HOL.Prolly.entails_iff_semantic
#print axioms HOL.Prolly.derives_iff_list
#print axioms HOL.Prolly.entails_iff_list
#print axioms DaslHOLProllyTest.unavailableNotRefuted
#print axioms DaslHOLProllyTest.entails
