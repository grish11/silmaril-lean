module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs

/-! Compose entry-local deletion with checked deletion on both incoming routes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition

open RVSDG (Tuple)
open Discovery.MemRef.CF (Programs lowerDiamond)

variable {args : List ValueSort} {cells : Nat}

/-- Recognize exactly an argument-addressed Store of an argument word
followed by Return. The entry boundary uses only the produced heap. -/
def asPrefixStore : Memory.Graph args → Option (PrefixStore args)
  | .store _ (.arg address) (.arg value) (.ret _ _) => some ⟨address, value⟩
  | _ => none

/-- Discover both route witnesses anew for the residual entry Store. -/
def rewriteResidual (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Option (Discovery.Result args) := do
  let store ← asPrefixStore entry
  Discovery.rewrite ⟨store, graph⟩ input

structure Result (cells : Nat) (args : List ValueSort) where
  entryDeleted : Nat
  allPathDeleted : Bool
  programs : Programs cells args

/-- First exhaust the entry-local selector. If the residual entry is
eligible and both routes check, emit the bare rewritten diamond. Otherwise
keep the native entry pass's emitted result. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) : Result cells args :=
  let repeated := Entry.lowerRepeated graph entry input
  match rewriteResidual graph repeated.entry input with
  | none => ⟨repeated.deleted, false, repeated.programs⟩
  | some result => ⟨repeated.deleted, true, { repeated.programs with
      optimized := lowerDiamond cells result.graph none }⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition
