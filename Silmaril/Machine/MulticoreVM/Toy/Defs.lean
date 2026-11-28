module

public import Silmaril.Machine.MulticoreVM.Defs

/-! # A register VM with dynamic cores -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Toy

abbrev ThreadId := Nat

inductive Instr where
  | add (amount : Nat)
  | emit
  | spawn (initialRegister : Nat) (program : List Instr)

/-- The local register and the remaining instructions of one core. -/
structure Core where
  reg : Nat
  program : List Instr

abbrev Config := ThreadId → Option Core

/-- A configuration with just one allocated core. -/
def init (thread : ThreadId) (core : Core) : Config :=
  fun t => if t = thread then some core else none

/-- Install a core, leaving every other slot as it was. -/
def put (cfg : Config) (thread : ThreadId) (core : Core) : Config :=
  fun t => if t = thread then some core else cfg t

/-- The auxiliary choice supplies exactly the child ID for a spawn. Missing or finished cores,
mismatched choices and occupied child IDs have no transition. Finished cores remain allocated. -/
def exec (thread : ThreadId) (child : Option ThreadId) (cfg : Config) :
    Option (Config × Fragment ThreadId Nat) := do
  let core ← cfg thread
  match core.program, child with
  | .add amount :: rest, none =>
    return (put cfg thread ⟨core.reg + amount, rest⟩, [])
  | .emit :: rest, none =>
    return (put cfg thread ⟨core.reg, rest⟩, [.event core.reg])
  | .spawn initialRegister program :: rest, some child =>
    match cfg child with
    | some _ => none
    | none =>
      return (put (put cfg thread ⟨core.reg, rest⟩) child ⟨initialRegister, program⟩,
        [.sync [thread, child]])
  | _, _ => none

abbrev step : Transition Config ThreadId (Option ThreadId) Nat := ofExecutor exec

end Silmaril.Machine.MulticoreVM.Toy
