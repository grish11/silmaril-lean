module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs
public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Defs

/-! # Bounded current-table discovery and replay for zero sampling -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

open PEG

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

/-- Match an actual zero-sample redex that still lacks an exact RHS
in its class. Unmatched rows are ineligible. -/
def enabled (zero : P [] .count) (s : Output P params results l) (i : Fin s.1) : Bool :=
  match ZeroSample.matchAt (g := s.2.graph) i zero with
  | none => false
  | some found => !checkCovered found s.2.classes

def enabledAt (zero : P [] .count) (s : Output P params results l) (address : Nat) : Bool :=
  if bound : address < s.1 then enabled zero s ⟨address, bound⟩ else false

def next (zero : P [] .count) (s : Output P params results l) : Option (Fin s.1) :=
  (List.finRange s.1).find? (enabled zero s)

def checkFixed (zero : P [] .count) (s : Output P params results l) : Bool :=
  (next zero s).isNone

/-- All actual matches in the current table have a covered RHS. -/
def Fixed (zero : P [] .count) (s : Output P params results l) : Prop :=
  ∀ (i : Fin s.1) (found : ZeroSample s.2.graph i zero), Covered found s.2.classes

/-- The family of visits uses the same policy as the executable driver. -/
def Visits (zero : P [] .count) : NormalForms.Family (Output P params results l) Nat :=
  fun address s target => target = visit zero s address

abbrev Stop := Extension.Worklist.Stop
abbrev Report := Extension.Worklist.Report Nat
abbrev Result (P : InstructionSet.{u,v} Data) (params results : List (Ty Data)) (l : Nat) :=
  Extension.Worklist.Result (Output P params results l) Nat

def driver (zero : P [] .count) : Extension.Worklist.Driver (Output P params results l) Nat :=
  ⟨fun s => (next zero s).map Fin.val, enabledAt zero, visit zero⟩

abbrev run (zero : P [] .count) : Nat → Output P params results l → Result P params results l :=
  (driver zero).run

abbrev replay (zero : P [] .count) : Output P params results l → List Nat → Option (Output P params results l) :=
  (driver zero).replay

abbrev checkStop (zero : P [] .count) (fuel : Nat) (state : Output P params results l) (report : Report) : Bool :=
  (driver zero).checkStop fuel state report

abbrev check (zero : P [] .count) : Nat → Output P params results l → Report → Option (Output P params results l) :=
  (driver zero).check

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
