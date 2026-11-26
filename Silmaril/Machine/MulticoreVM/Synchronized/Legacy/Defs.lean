module

public import Silmaril.Machine.MulticoreVM.Synchronized.Defs
public import Silmaril.Machine.MulticoreVM.Toy.Defs

/-! # Embedding the old add, emit and spawn fragment -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Synchronized.Legacy

open Silmaril.Semantics.ConcurrentTrace (LocalLetter Letter Word)

mutual
  /-- A legacy spawn recursively translates its child's program. -/
  def instr : Toy.Instr → Instr
    | .add n => .add n
    | .emit => .emit
    | .spawn reg child => .spawn reg (instructions child)
  termination_by structural instruction => instruction

  def instructions : List Toy.Instr → List Instr
    | [] => []
    | head :: tail => instr head :: instructions tail
  termination_by structural code => code
end

def localState (core : Toy.Core) : Local :=
  ⟨core.reg, instructions core.program⟩

/-- Old allocated slots become runnable. The initial shared words are arbitrary. -/
def config (words : Shared) (old : Toy.Config) : Config :=
  ⟨words, fun thread => (old thread).map fun core => .runnable (localState core)⟩

def choice : Option ThreadId → Choice
  | none => .run []
  | some child => .spawn child

def schedule (old : Schedule ThreadId (Option ThreadId)) : Schedule ThreadId Choice :=
  old.map fun decision => ⟨decision.thread, choice decision.choice⟩

def localLetter : LocalLetter ThreadId Nat → LocalLetter ThreadId Event
  | .event value => .event (.localOutput value)
  | .sync participants => .sync participants

def letter : Letter ThreadId Nat → Letter ThreadId Event
  | .event thread value => .event thread (.localOutput value)
  | .sync participants => .sync participants

end Silmaril.Machine.MulticoreVM.Synchronized.Legacy
