module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Defs

/-! # Register VM with spawn and keyed thread synchronization -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Synchronized

abbrev ThreadId := Nat
abbrev Address := Nat
abbrev Shared := Address → Nat

inductive Instr where
  | add (amount : Nat)
  | emit
  | spawn (initialRegister : Nat) (program : List Instr)
  | store (address : Address) (value : Nat)
  | wait (address : Address) (expected : Nat)
  | wake (address : Address) (limit : Nat)
  | yield

structure Local where
  reg : Nat
  program : List Instr

abbrev Slot := ThreadSync.ThreadState Address Local
abbrev Config := ThreadSync.Config ThreadId Address Nat Local
abbrev Event := ThreadSync.Event ThreadId Address Nat Nat

inductive Choice where
  | run (waiters : List ThreadId)
  | spawn (child : ThreadId)

/-- A runnable thread with instructions remaining can receive a slot. Parked threads
remain allocated and hold their saved continuation. -/
def Runnable : ThreadId → Slot → Prop
  | _, .runnable localState => localState.program ≠ []
  | _, .parked .. => False

/-- Reuse the sibling VM for every operation except allocation. Wait sets the register to one
on mismatch and zero on wake. Wake writes the number of selected waiters to the register. -/
def program : ThreadSync.Program ThreadId Address Nat Local Nat
  | _, ⟨reg, .add amount :: rest⟩ => some (.localStep ⟨reg + amount, rest⟩ none)
  | _, ⟨reg, .emit :: rest⟩ => some (.localStep ⟨reg, rest⟩ (some reg))
  | _, ⟨reg, .store address value :: rest⟩ => some (.store address value ⟨reg, rest⟩)
  | _, ⟨_, .wait address expected :: rest⟩ => some (.wait address expected ⟨1, rest⟩ ⟨0, rest⟩)
  | _, ⟨_, .wake address limit :: rest⟩ => some (.wake address limit fun count => ⟨count, rest⟩)
  | _, ⟨reg, .yield :: rest⟩ => some (.yield ⟨reg, rest⟩)
  | _, _ => none

/-- A spawn has a separate choice and requires a free child slot. Its fragment has the
same participant list as the old register VM. All other actions use the sibling executor. -/
def exec (thread : ThreadId) (choice : Choice) (cfg : Config) :
    Option (Config × Fragment ThreadId Event) :=
  match choice with
  | .run waiters => ThreadSync.exec program thread waiters cfg
  | .spawn child => do
    let some (.runnable ⟨reg, .spawn initialRegister childProgram :: rest⟩) := cfg.threads thread | none
    if (cfg.threads child).isSome then none else
      return ((cfg.put thread (.runnable ⟨reg, rest⟩)).put child (.runnable ⟨initialRegister, childProgram⟩),
        [.sync [thread, child]])

abbrev step : Transition Config ThreadId Choice Event := ofExecutor exec

end Silmaril.Machine.MulticoreVM.Synchronized
