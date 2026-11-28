module

public import Silmaril.Machine.SQLite.VirtualMachine.Defs

/-! The UTF-8 String8 rewrite, modelled as a change of fetched code cell.
In the pinned source OP_String8 rewrites itself into OP_String and caches
the encoded length. Here the text is already decoded, so the cached form
models only the change of opcode. Encoding conversion, allocation and
length failures, tracing and Init/Once counters are outside this model. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Mutable

open Silmaril.Formats.Sqlite

inductive Cell where
  | original (instruction : Instruction)
  | cachedString (text : String) (destination : Nat)
  deriving DecidableEq

def Cell.erase : Cell → Instruction
  | .original instruction => instruction
  | .cachedString text destination => .string8 text destination

def Cell.cache : Cell → Cell
  | .original (.string8 text destination) => .cachedString text destination
  | cell => cell

structure Configuration where
  state : State
  code : Array Cell

def Configuration.ofProgram (code : Program) (state : State) : Configuration :=
  ⟨state, code.map .original⟩

def Configuration.erased (cfg : Configuration) : Program := cfg.code.map Cell.erase

/-- The model's representation invariant connects both code and VM state. -/
def Represents (cfg : Configuration) (program : Program) (state : State) : Prop :=
  cfg.erased = program ∧ cfg.state = state

def step (db : Database) (cfg : Configuration) : Except Fault Configuration :=
  if cfg.state.halted.isSome then .error .alreadyHalted else
    match cfg.code[cfg.state.pc]? with
    | none => .error (.programCounter cfg.state.pc)
    | some cell =>
        (Vdbe.execute db cell.erase cfg.state).map fun after =>
          ⟨after, cfg.code.setIfInBounds cfg.state.pc cell.cache⟩

structure Execution where
  result : RunResult
  code : Array Cell

def run (db : Database) : Nat → Configuration → Execution
  | fuel, cfg =>
      if cfg.state.halted.isSome then ⟨.halted cfg.state, cfg.code⟩ else
        match fuel with
        | 0 => ⟨.exhausted cfg.state, cfg.code⟩
        | fuel + 1 =>
          match step db cfg with
          | .error fault => ⟨.fault fault cfg.state, cfg.code⟩
          | .ok after => run db fuel after

end Silmaril.Machine.SQLite.VirtualMachine.Mutable
